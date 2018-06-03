------------------------ MODULE networkSpecification ------------------------

(* This is a TLA module specifying the Communicationsing layer of SIMIX. 
   It is used to verify the soundness of the DPOR reduction algorithm
   used in the model-checker. 

   If you think you found a new independence lemma, add it to this
   file and relaunch TLC to check whether your lemma actually holds.
   *)
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANTS Mailboxes, Addr, Actors, Mutexes, ValTrue, ValFalse, SendIns, ReceiveIns, WaitIns, 
          TestIns, LocalIns, LockIns, UnlockIns,  MwaitIns
VARIABLES Communications, memory, pc, waitingQueue, Requests, AcState

NoActor == CHOOSE p : p \notin Actors
NoAddr == CHOOSE a : a \notin Addr

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {SendIns, ReceiveIns, WaitIns, TestIns, LocalIns,LockIns, UnlockIns, MwaitIns}

Comm == [id:Nat,
         mb:Mailboxes,
         status:{"send","receive","ready","done"},
         src:Actors,
         dst:Actors,
         data_src:Addr,
         data_dst:Addr]

           
getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e


isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 

isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE

Remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))
    
ASSUME ValTrue \in Nat
ASSUME ValFalse \in Nat

(* The set of all the instructions *)
ASSUME Partition({SendIns, ReceiveIns, WaitIns, TestIns, LocalIns,LockIns, UnlockIns, MwaitIns}) 


(* Let's keep everything in the right domains *)
TypeInv == /\ Communications \subseteq Comm
           /\ memory \in [Actors -> [Addr -> Nat]]
           /\ pc \in [Actors -> Instr]

(* The set of all communications waiting at mb *)
(* ----- mailbox is updated automatically when updating the Communications  *)
mailbox(mb) == {comm \in Communications : comm.mb=mb /\ comm.status \in {"send","receive"}}


(* The set of memory addresses of a Actoress being used in a communication *)
CommBuffers(Aid) == 
  {c.data_src: c \in { y \in Communications: y.status /= "done" /\ (y.src = Aid \/ y.dst = Aid)}} 
\cup {c.data_dst: c \in { y \in Communications: y.status /= "done" /\ (y.src = Aid \/ y.dst = Aid)}}

(* This is a AsyncSend step of the system *)
(* Aid: the Actoress ID of the AsyncSender *)
(* mb: the rendez-vous point where the "send" communication request is going to be pushed *)
(* data_r: the address in the AsyncSender's memory where the data is stored *)
(* comm_r: the address in the AsyncSender's memory where to store the communication id *)
AsyncSend(Aid, mb, data_r, comm_r) == 
  /\ mb \in Mailboxes
  /\ Aid \in Actors
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[Aid] \in SendIns
  /\ AcState[Aid] /= "blocked"   
   
     (* A matching AsyncReceive request exists in the rendez-vous *)
     (* Complete the Sender fields and set the communication to the ready state *)
  /\ \/ \exists c \in mailbox(mb):
          /\ c.status="receive"
          /\ \forall d \in mailbox(mb): d.status="receive" => c.id <= d.id
          /\ Communications' = 
               (Communications \ {c}) \cup {[c EXCEPT
                                       !.status = "ready",
                                       !.src = Aid,
                                       !.data_src = data_r]}
          (* Use c's existing communication id *)
          /\ memory' = [memory EXCEPT ![Aid][comm_r] = c.id]
               
     
     (* No matching AsyncReceive communication request exists. *)
     (* Create a AsyncSend request and push it in the Communications. *)
     \/ /\ ~ \exists c \in mailbox(mb): c.status = "receive" 
        /\ LET comm ==  
                 [id |-> Cardinality(Communications)+1, 
                  mb |-> mb,
                  status |-> "send", 
                  src |-> Aid,
                  dst |-> NoActor, 
                  data_src |-> data_r,
                  data_dst |-> NoAddr]
           IN
             /\ Communications' = Communications \cup {comm}
             /\ memory' = [memory EXCEPT ![Aid][comm_r] = comm.id]           
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<  waitingQueue,Requests, AcState>>
(* This is a receive step of the system *)
(* Aid: the Actoress ID of the receiver *)
(* mb: the Rendez-vous where the "receive" communication request is going to be pushed *)
(* data_r: the address in the receivers's memory where the data is going to be stored *)
(* comm_r: the address in the receivers's memory where to store the communication id *)
AsyncReceive(Aid, mb, data_r, comm_r) == 
  /\ mb \in Mailboxes
  /\ Aid \in Actors
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[Aid] \in ReceiveIns
  /\ AcState[Aid] /= "blocked"   
  
     (* A matching AsyncSend request exists in the rendez-vous *)
     (* Complete the receiver fields and set the communication to the ready state *)
  /\ \/ \exists c \in mailbox(mb):
          /\ c.status="send"
          /\ \forall d \in mailbox(mb): d.status="send" => c.id <= d.id
          /\ Communications' = 
               (Communications \ {c}) \cup {[c EXCEPT
                                       !.status = "ready",
                                       !.dst = Aid,
                                       !.data_dst = data_r]}
          (* Use c's existing communication id *)
          /\ memory' = [memory EXCEPT ![Aid][comm_r] = c.id]
               
     
     (* No matching AsyncSend communication request exists. *)
     (* Create a AsyncReceive request and push it in the Communications. *)
     \/ /\ ~ \exists c \in mailbox(mb): c.status = "send" 
        /\ LET comm ==  
                 [id |-> Cardinality(Communications)+1,
                  status |-> "receive", 
                  dst |-> Aid, 
                  data_dst |-> data_r]
           IN
             /\ Communications' = Communications \cup {comm}
             /\ memory' = [memory EXCEPT ![Aid][comm_r] = comm.id]           
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue,Requests, AcState>>

(* Wait for at least one communication from a given list to complete *)
(* Aid: the Actoress ID issuing the wait *)
(* comms: the list of addresses in the Actoress's memory where the communication ids are stored *)
Wait(Aid, comms) ==
  /\ Aid \in Actors
  /\ pc[Aid] \in WaitIns
  /\ AcState[Aid] /= "blocked"   
  
  /\ \E comm_r \in comms, c \in Communications: c.id = memory[Aid][comm_r] /\
     \/ /\ c.status = "ready"
        /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src]]
        /\ Communications' = (Communications \ {c}) \cup {[c EXCEPT !.status = "done"]}
     \/ /\ c.status = "done"
        /\ UNCHANGED <<memory,Communications>>
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests, AcState>>

(* Test if at least one communication from a given list has completed *)
(* Aid: the Actoress ID issuing the wait *)
(* comms: the list of addresses in the Actoress's memory where the communication ids are stored *)
(* ret_r: the address in the Actoress's memory where the result is going to be stored *)
Test(Aid, comms, ret_r) ==
  /\ ret_r \in Addr
  /\ Aid \in Actors
  /\ pc[Aid] \in TestIns
  /\ AcState[Aid] /= "blocked"   
  
  /\ \/ \E comm_r \in comms, c\in Communications: c.id = memory[Aid][comm_r] /\
        \/ /\ c.status = "ready"
           /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src],
                                        ![Aid][ret_r] = ValTrue]
           /\ Communications' = (Communications \ {c}) \cup {[c EXCEPT !.status = "done"]}
        \/ /\ c.status = "done"
           /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValTrue]
           /\ UNCHANGED <<Communications>>
           
           
     \/ ~ \exists comm_r \in comms, c \in Communications: c.id = memory[Aid][comm_r]
        /\ c.status \in {"ready","done"}
        /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValFalse]
        /\ UNCHANGED <<Communications>> 
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests, AcState>>
(* Local instruction execution *)
Local(Aid) ==
    /\ Aid \in Actors
    /\ pc[Aid] \in LocalIns
    /\ AcState[Aid] /= "blocked"   
    
   (* /\ memory' \in [Actor -> [Addr -> Nat]]
    /\ \forall p \in Actor, a \in Addr: memory'[p][a] /= memory[p][a]
       => p = Aid /\ a \notin CommBuffers(Aid) *)
    /\ memory'= [memory EXCEPT ![Aid]  = [Addr -> Nat]]
    /\ \forall a \in Addr: memory'[Aid][a] /= memory[Aid][a]
       => a \notin CommBuffers(Aid)
    /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
    /\ UNCHANGED <<Communications, waitingQueue,Requests, AcState>>
----------------------------------------------------------------------------------------------------------------

MutexAsyncLock(Aid, mid) ==
   /\ AcState[Aid] /= "blocked"   
   /\ Aid \in Actors
   /\ pc[Aid] \in LockIns
   /\ mid \in Mutexes
   /\ \/ /\ ~isMember(Aid, waitingQueue[mid]) 
         /\ Requests'  = [Requests EXCEPT ![Aid]= Requests[Aid] \cup {mid}]
         /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Append(waitingQueue[mid], Aid)] 
      \/ /\ isMember(Aid, waitingQueue[mid]) 
         /\ UNCHANGED <<waitingQueue, Requests>>  
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   /\ UNCHANGED <<AcState, Communications, memory>>

(* When a Actoress <Aid> does a valid unlock() on Mutex <mid>, then:
 * - If <Aid> is the owner (head of waitingQueue), that's a naive unlock and we 
 *     remove all linking between Aid and mid that was created in ilock().
 * - If <Aid> is not the owner, that's a cancel, and we remove the linking anyway.
 *
 * - If <Aid> is not even in the waitingQueue (it did not ask for the <mid> previously),
 *   that's not enabled, and <Aid> is blocked. Too bad for it.
 *)
 
 (*AcState well be removed when adding MutexTest*)
 
MutexUnlock(Aid, mid) ==
   /\ AcState[Aid] /= "blocked"   
   /\ Aid \in Actors
   /\ mid \in Mutexes
   /\ pc[Aid] \in UnlockIns
   
   (* If the request was previously posted (either owner or not) remove any linking *)
   /\ isMember(Aid, waitingQueue[mid]) 
   /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Remove(Aid,waitingQueue[mid])]
   /\ Requests' = [Requests EXCEPT ![Aid] = Requests[Aid] \ {mid}]
   (* If not a member, the transition is not enabled *)
   
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   /\ UNCHANGED <<AcState,Communications, memory >>
   
(* When a Actoress <Aid> does a mutex_wait on <mid>, 
 *  - If <Aid> is the owner of <mid>, then MutexWait is fined
 *  - If not, the transition is not enabled
 *  - The parameter mid will be replaced by a request when adding MutexTest
 *)


MutexWait(Aid, mid) ==
/\ AcState[Aid] /= "blocked"   
/\ Aid \in Actors
/\ pc[Aid] \in MwaitIns
/\ \/  /\ mid \in Requests[Aid] 
       /\ \/ /\ isHead(Aid, waitingQueue[mid])
             /\ UNCHANGED <<AcState>>
          \/ /\ ~isHead(Aid, waitingQueue[mid])
             /\  AcState' = [AcState EXCEPT ![Aid] = "blocked"]
   \/  /\ mid \notin Requests[Aid] /\ UNCHANGED  <<AcState>>
/\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
/\ UNCHANGED << waitingQueue, Requests, Communications, memory>>




----------------------------------------------------------------------------------------------------------------


(* Initially there are no messages in the Communications and the memory can have anything in their memories *)

Init == /\ Communications = {}
        (*/\ memory \in [Actors -> [Addr -> Nat]*)
        
        (*Set memory for run model*)
        /\ memory \in [Actors -> [Addr -> {0,1,2,3,4}]]
        /\ waitingQueue = [i \in Mutexes |-> << >>]
        /\ Requests = [i \in Actors |-> << >>]
        /\ AcState = [i \in Actors |-> "running"]
        (*/\ pc = CHOOSE f : f \in [Actor -> Instr]*)
         /\ pc = CHOOSE f \in [Actors -> Instr] : TRUE
        


Next == \exists p \in Actors, data_r \in Addr, comm_r \in Addr, comms \in SUBSET Addr, mb \in Mailboxes,
                ret_r \in Addr, ids \in SUBSET Communications, mutex \in Mutexes:
          \/ AsyncSend(p, mb, data_r, comm_r)
          \/ AsyncReceive(p, mb, data_r, comm_r)
          \/ Wait(p, comms)
          \/ Test(p, comm_r, ret_r)
          \/ Local(p)
          \/ MutexAsyncLock(p,mutex)
          \/ MutexUnlock(p,mutex)
          \/ MutexWait(p, mutex)
          (*\/ Mtest(p,mutex)   *)  
          
Spec == Init /\ [][Next]_<<AcState, pc, Communications, memory, waitingQueue, Requests >>
-----------------------------------------------------------------------------------------------------------------

------------------------------------------
(* Independence operator *)
I(A,B) == ENABLED A /\ ENABLED B => /\ A => (ENABLED B)'
                                    /\ B => (ENABLED A)'
                                    /\ A \cdot B \equiv B \cdot A
                                    
(* Independence of iAsyncSend / iAsyncReceive steps *)
THEOREM \forall p1, p2 \in Actors: \forall mb1, mb2 \in Mailboxes: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ ENABLED AsyncSend(p1, mb1, data1, comm1)
        /\ ENABLED AsyncReceive(p2, mb2, data2, comm2)
        => I(AsyncSend(p1, mb1, data1, comm1), AsyncReceive(p2, mb2, data2, comm2))

(* Independence of iAsyncSend and Wait *)
THEOREM \forall p1, p2 \in Actors: \forall data, comm1, comm2 \in Addr:
        \forall mb \in Mailboxes: \exists c \in Communications:
        /\ p1 /= p2
        /\ c.id = memory[p2][comm2]
        /\ \/ (p1 /= c.dst /\ p1 /= c.src)
           \/ (comm1 /= c.data_src /\ comm1 /= c.data_dst)
        /\ ENABLED AsyncSend(p1, mb, data, comm1)
        /\ ENABLED Wait(p2, comm2)
        => I(AsyncSend(p1, mb, data, comm1), Wait(p2, comm2)) 

(* Independence of iAsyncSend's in different rendez-vous *)
THEOREM \forall p1, p2 \in Actors: \forall mb1, mb2 \in Mailboxes: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ mb1 /= mb2
        /\ ENABLED AsyncSend(p1, mb1, data1, comm1)
        /\ ENABLED AsyncSend(p2, mb2, data2, comm2)
        => I(AsyncSend(p1, mb1, data1, comm1),
             AsyncSend(p2, mb2, data2, comm2))

(* Independence of iAsyncReceive's in different rendez-vous *)
THEOREM \forall p1, p2 \in Actors: \forall mb1, mb2 \in Mailboxes: 
        \forall data1, data2, comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ mb1 /= mb2
        /\ ENABLED AsyncReceive(p1, mb1, data1, comm1)
        /\ ENABLED AsyncReceive(p2, mb2, data2, comm2)
        => I(AsyncReceive(p1, mb1, data1, comm1),
             AsyncReceive(p2, mb2, data2, comm2))

(* Independence of Wait of different Actoresses on the same comm *)
THEOREM \forall p1, p2 \in Actors: \forall comm1, comm2 \in Addr:
        /\ p1 /= p2
        /\ comm1 = comm2
        /\ ENABLED Wait(p1, comm1)
        /\ ENABLED Wait(p2, comm2)
        => I(Wait(p1, comm1), Wait(p2, comm2))
        
====
\* Generated at Thu Feb 18 13:49:35 CET 2010


=============================================================================
\* Modification History
\* Last modified Sun Jun 03 15:42:42 CEST 2018 by diep-chi
\* Created Fri Jan 12 18:32:38 CET 2018 by diep-chi
