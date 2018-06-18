----------------------------------------- MODULE networkSpecification -------------------------------------------------


(* This specification formally describes (build formal model of) programs/system that are simulated in SimGrid, 
    it focuses on modeling the states and actions of the system, firing an action at a current state leads to a next state
                   
                   current state
                        |
                        |
                        | action
                        |
                        v
                   next state 
                   
  - A state is represented by 4 variables: Communications, memory, pc, waitingQueue and Requests
    + Communications is the set of all communications in the system
    + memory is indexed by Actors' id, memory[Aid] is used to store id of communications, id of requests, values of local vairables 
    + pc is indexed by id of Actors, pc[Aid] represents the program counter of actor Aid, changed  after firing each action 
    + waitinQueue is indexed by mutexes, waitingQueue[mid] is a fifo queue that remembers which actors have required it
    + Requests is indexed by Actors' id, Requests[Aid] is the set of all the mutex ids requested by the actor Aid   
   
  - Actions are structured in 3 subsystems:
    - the Local actions :  Local, 
    - the Communication actions: AsyncSend, AsyncReceive, Wait, Test,
    - the Synchronization actions: MutexAsyncLock, MutexUnLock, MutexTest and MutexWait.
   *)
   
(*---------------------------- GENERAL CONSTANTS, VARIABLES, FUNCTIONS  --------------------------------------------*)
    
EXTENDS Integers , Naturals, Sequences, FiniteSets

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y

(*---  FUNCTIONS ON SEQUENCES USED FOR FIFO QUEUES -- *)
           
(* getIndex(e,q) gives the position of e in the sequence q *)           
getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e

(*isHead(m,q) checks whether m is the first element in the sequence q *)
isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 
                     
(* Remove(e,q) removes e from sequence q*)                     
Remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))
                                                               
(*isMember(m, q) checks whether m is a member of sequence q*) 
isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE

   
(* ---------------------------- GENERAL CONSTANTS, VARIABLES and FUNCTIONS OF THE MODEL --------------------------- *)
CONSTANTS Mailboxes, Addr, Actors, Mutexes, ValTrue, ValFalse, SendIns, ReceiveIns, WaitIns, 
          TestIns, LocalIns, LockIns, UnlockIns,  MwaitIns, MtestIns
          
VARIABLES Communications, memory, pc,  waitingQueue, Requests

NoActor == CHOOSE p : p \notin Actors
NoAddr == CHOOSE a : a \notin Addr

Instr ==UNION {SendIns, ReceiveIns, WaitIns, TestIns, LocalIns ,LockIns, UnlockIns, MwaitIns, MtestIns}

ASSUME Partition({SendIns, ReceiveIns, WaitIns, TestIns, LocalIns , LockIns, UnlockIns, MwaitIns, MtestIns}) 

ASSUME ValTrue \in Nat
ASSUME ValFalse \in Nat


(* Comm type is declared as a structure *)  
Comm == [id:Nat,
         mb:Mailboxes,
         status:{"send","receive","ready","done"},
         src:Actors,
         dst:Actors,
         data_src:Addr,
         data_dst:Addr]

(* Let's keep everything in the right domains, just for checking *)
TypeInv == /\ Communications \subseteq Comm
           /\ memory \in [Actors -> [Addr -> Nat]]
           /\ pc \in [Actors -> Instr]





(* ---------------------------------------------COMMUNICATION SUBSYSTEM -----------------------------------*)


(* mailbox(mb) gives all pending requests posted on it *)
mailbox(mb) == {comm \in Communications : comm.mb=mb /\ comm.status \in {"send","receive"}}


(* The set of memory addresses of a Actor being used in a communication *)
CommBuffers(Aid) == 
  {c.data_src: c \in { y \in Communications: y.status /= "done" /\ (y.src = Aid \/ y.dst = Aid)}} 
\cup {c.data_dst: c \in { y \in Communications: y.status /= "done" /\ (y.src = Aid \/ y.dst = Aid)}} 



                           (*-------------------- COMMUNICATION ACTIONS -------------------*)

(* AsyncSend(Aid,mb,data_r,comm_r):  
    the actor <Aid> sends a "send" request to the maibox <mb>. 
    If a pending "receive" request already exists, they are combined to create a "ready" communication in the set Communications, 
    otherwise a new communication with "send" status is created,
    address <data_r> of Actor <Aid> contains the data to transmit,
    and memory address <comm_r> of Actor <Aid> is assigned the id of the communication 

  Parameters:
    - Aid: the Actor ID of the sender 
    - mb: the mailbox where the "send" communication request is pushed 
    - data_r: the address in the AsyncSender's memory where the data to transmit is stored 
    - comm_r: the address in the AsyncSender's memory where to store the communication id *)

AsyncSend(Aid, mb, data_r, comm_r) == 
  /\ Aid \in Actors
  /\ mb \in Mailboxes
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[Aid] \in SendIns
   
     (* If a matching "receive" request exists in the mailbox(mb), choose the oldest one and
        complete the Sender fields and set the communication to the "ready" state *)
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
               
     
     (* Otherwise (i.e. no matching AsyncReceive communication request exists,
        create a AsyncSend request and push it in the set Communications. *)
     \/ /\ ~ \exists c \in mailbox(mb): c.status = "receive" 
        /\ LET comm ==  
                 [id |-> Cardinality(Communications)+1, 
                  mb |-> mb,
                  status |-> "send", 
                  src |-> Aid,
                  dst |-> NoActor,  (* destination is randomly chosen ? *) 
                  data_src |-> data_r,
                  data_dst |-> NoAddr]
           IN
             /\ Communications' = Communications \cup {comm}
             /\ memory' = [memory EXCEPT ![Aid][comm_r] = comm.id]      
  (* AsyncSend is never blocking *)             
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<  waitingQueue,Requests>>
  
 
 
(* AsyncReceive(Aid,mb,data_r,comm_r): the actor <Aid> sends a "receive" request to the mailbox <mb>.
   If there is a pending "send" request on the same mailbox <mb>, they are combined to create a "ready" communication, 
   otherwise a new communication is created with "receive" status.
   the address <data_r> 
   the address <comm_r> of <Aid> is assigned the id of the communication,
   
  Parameters: 
    - Aid: the Actor ID of the receiver 
    - mb: the mailbox where the "receive" communication request is going to be pushed 
    - data_r: the address in the receivers's memory where the data is going to be stored 
    - comm_r: the address in the receivers's memory where to store the communication id *)

AsyncReceive(Aid, mb, data_r, comm_r) == 
  /\ Aid \in Actors
  /\ mb \in Mailboxes
  /\ data_r \in Addr
  /\ comm_r \in Addr
  /\ pc[Aid] \in ReceiveIns
 
     (* If a matching "send" request exists in the mailbox mb, choose the oldest one and,
        complete the receiver's fields and set the communication to the "ready" state *)
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
               
     
     (* Otherwise (i.e. no matching AsyncSend communication request exists),  
        create a "receive" request and push it in the Communications. *)
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
  /\ UNCHANGED <<waitingQueue,Requests>>




(* Wait(Aid,comms):  Actor <Aid> waits for at least one communication from a given set <comms> to complete 
    If the communication is "ready" for being processed, data is transfered from the source actor to the destination actor, 
    from/to the addresses specified in the communication, 
       if it is already "done", there is nothing to do.
    The function is blocking when no communication is "ready" or "done".   
 Parameters:
    - Aid: the Actor's ID issuing the wait request
    - comms: the list of addresses in the Actor's memory where the communication ids are stored 
*)

Wait(Aid, comms) ==
  /\ Aid \in Actors
  /\ pc[Aid] \in WaitIns
 
  /\ \E comm_r \in comms, c \in Communications: c.id = memory[Aid][comm_r] /\
     \/ /\ c.status = "ready"
        (*data is transfered to destination, then update status of the communication to "done" *)
        /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src]]
        /\ Communications' = (Communications \ {c}) \cup {[c EXCEPT !.status = "done"]}
     \/ /\ c.status = "done"
        /\ UNCHANGED <<memory,Communications>>
  (* in both cases, pc[Aid] is incremented *) 
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests>>
 (* otherwise i.e. no communication in <comms> is "ready" or "done", Wait is blocking *)



(* Test(Aid, comms, ret_r): Actor <Aid> waits for at least one communication from a given list <comms> to complete,
    and returns the boolean result at memory adress <ret_r>.
    The function is very similar to Wait, but returns ret_r as a result, and is never blocking.
    Parameters
    - Aid: the Actor ID issuing the test request 
    - comms: the list of addresses in the Actor's memory where the communication ids are stored 
    - ret_r: the address in the Actor memory where the boolean result is going to be stored *)

Test(Aid, comms, ret_r) ==
  /\ Aid \in Actors
  /\ ret_r \in Addr
  /\ pc[Aid] \in TestIns
  /\ \/ \E comm_r \in comms, c\in Communications: c.id = memory[Aid][comm_r] /\
        (* If the communication is "ready" the data is transfered, return ValTrue *)
        \/ /\ c.status = "ready"
           /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src],
                                        ![Aid][ret_r] = ValTrue]
           /\ Communications' = (Communications \ {c}) \cup {[c EXCEPT !.status = "done"]}
        (* else if the cummunication is already done, keep Communications unchanged, return ValTrue *)   
        \/ /\ c.status = "done"
           /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValTrue]
           /\ UNCHANGED <<Communications>>
           
        (* if no communication is "ready" or "done", return ValFalse *)   
     \/ ~ \exists comm_r \in comms, c \in Communications: c.id = memory[Aid][comm_r]
        /\ c.status \in {"ready","done"}
        /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValFalse]
        /\ UNCHANGED <<Communications>> 
  (* Test is non-blocking since in all cases pc[AId] is incremented *)
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests>>
  

(* -------------------------------- SYNCHRONIZATION SUBSYSTEM ----------------------------------------------------*)
                                
(* MutexAsyncLock(Aid, mid, req_a) : Actor <Aid> is requesting a lock on mutex <mid>. If allowed, address <req_a> stores the mutex id <mid>.    
- If the actor <Aid> has no pending request on mutex <mid>, a new one is created 
        - add pair [mid,req_a] in Request[Aid]
        - store <mid> in memory[Aid][req_a], i.e. local address <req_a> is assigned value <mid>
        - enqueue <Aid> in waitingQueue[mid]
 The operation is non-blocking (pc[Aid] is modified in any case)       
*) 

  
  MutexAsyncLock(Aid, mid, req_a) ==
   /\ Aid \in Actors
   /\ pc[Aid] \in LockIns
   /\ mid \in Mutexes
   /\ req_a \in Addr
         (* if Actor <Aid> has no pending request on mutex <mid>, create a new one *)      
   /\ \/ /\ ~isMember(Aid, waitingQueue[mid])
         /\  Requests'  = [Requests EXCEPT ![Aid]= Requests[Aid] \cup {mid}]
         /\  memory' = [memory EXCEPT ![Aid][req_a] = mid]  
         /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Append(waitingQueue[mid], Aid)]
         (* otherwise i.e. actor <Aid> alreadly has a pending request on mutex <mid>, keep the variables unchanged *)          
      \/ /\ isMember(Aid, waitingQueue[mid]) 
         /\ UNCHANGED <<waitingQueue,  memory, Requests>>  
   (* MutexAsyncLock is never blocking, in any case, pc[Aid] is incremented *) 
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   /\ UNCHANGED <<Communications>>
       
  
  
(* MutexUnlock(Aid,mid): the Actor <Aid> wants to release the mutex <mid>
    A "valid" unlock occurs when <Aid> is in waitingQueue[mid] 
    - it is either a normal unlock when <Aid> owns <mid> (it is head of waitingQueue[mid]) 
    - or a cancel otherwise. 
    In both cases all links between <mid> and <Aid> are removed in waitingQueue[mid] and Requests[Aid] 
   An "invalid" unlock occurs when <Aid> is not in waitingQueue[mid]    
     that's not enabled, and in this case <Aid> is blocked (pc[Aid] is not modified in this case).
 *)
 
MutexUnlock(Aid, mid) ==
   /\ Aid \in Actors
   /\ mid \in Mutexes
   /\ pc[Aid] \in UnlockIns
   
   (* If <Aid> makes a "valid" unlock on <mid> (either owner or not) remove any linking between them *)
   /\ isMember(Aid, waitingQueue[mid]) 
   /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Remove(Aid,waitingQueue[mid])]
   /\ Requests' = [Requests EXCEPT ![Aid] = Requests[Aid] \ {mid }]
   /\ UNCHANGED <<memory, Communications>>
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   (* Otherwise, the transition is not enabled and Actor <Aid> is blocked *)
   
   
(* MutexWait(Aid,req_a): Actor <Aid> waits for lock request <req_a>, 
  - if there is a req in Request[Aid] whose mid is <req_a>, and <Aid> is the owner of this mutex mid (head of waitingQUeue[req.id]), 
    then MutexWait is enabled
  - otherwise the transition is not enabled.
  MutexWait is thus blocking until <Aid> owns the mutex 
 *)

MutexWait(Aid, req_a) == 
/\ Aid \in Actors
/\ req_a \in Addr
/\ pc[Aid] \in MwaitIns
    (* If req_a is the id of a Request of Actor <Aid>, and <Aid> is the owner of this mutex, <Aid> proceeds and increment its pc *) 
/\ \E req \in Requests[Aid]: req = memory[Aid][req_a] /\ isHead(Aid, waitingQueue[req])
/\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
/\ UNCHANGED << memory, waitingQueue, Requests, Communications>>
(* otherwise <Aid> is blocked, pc[Aid] is unmodified *)  


(* MutexTest(Aid,req_a, test_r): actor <Aid> tests if he is the owner of the mutex of mid <req_a> 
            (i.e. he is the head of the mutex waitingQueue)
            and stores the boolean result at address <tesr_a> 
            MutexTest is non-blocking (in any case pc[Aid] is modified).
            *)
MutexTest(Aid, req_a,test_a) ==
  /\ Aid \in Actors
  /\ pc[Aid] \in MtestIns
  /\ test_a \in Addr
  /\  \E req \in  Requests[Aid]: req = memory[Aid][req_a]/\ 
       (* If the actor is the owner then return true *)
        \/ /\ isHead(Aid,waitingQueue[req])
           /\ memory' = [memory EXCEPT ![Aid][test_a] = ValTrue]
       (*else if it is not the onwer then return false *)
        \/ /\ ~isHead(Aid, waitingQueue[req])
           /\ memory' = [memory EXCEPT ![Aid][test_a] = ValFalse] 
           
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests, Communications>>


(* ---------------- LOCAL SUBSYSTEM ----------------------------------------------------------------------------------------- *)


(* A local computaion of Actor <Aid> can change the value of this Actor's memory at any address, 
    but not where communication's ids are strored      *)

Local(Aid) ==
    /\ Aid \in Actors
    /\ pc[Aid] \in LocalIns
    
    (*change value of memory[Aid][a] *)
    /\ memory' \in [Actors -> [Addr -> {0,1,2,3,4,5}]]
    /\ \forall p \in Actors, a \in Addr: memory'[p][a] /= memory[p][a]
    (* ensure that memory[Aid][a] is not where actor Aid strores communication *)
       => p = Aid /\ a \notin CommBuffers(Aid)
    /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
    /\ UNCHANGED <<Communications, waitingQueue,Requests>>


--------------------------------------------------------------------------------------------------------------------------------
                                    (*SET INITIAL VALUES FOR THE VARIABLES, INDICATE NEXT ACTIONS *)
                                    
                                    
(* Initially there are no Communications, no requests on the mutexes, 
memory has random values *)

Init == /\ Communications = {}
        (*/\ memory \in [Actors -> [Addr -> Nat]*)
        
        (*Set memory for running model*)
        /\ memory \in [Actors -> [Addr -> {0}]]
        
        /\ waitingQueue = [i \in Mutexes |-> <<>>] 
        /\ Requests = [i \in Actors |-> {}]
        (*/\ pc = CHOOSE f \in [Actors -> Instr] : TRUE*)
        /\ pc = [a \in Actors |-> "lock"] 
        
        
(* Next indicates the possible actions that could be fired at a state  *)
Next == \exists actor \in Actors, data_r \in Addr, comm_r \in Addr, req \in Addr, test_r \in Addr, comms \in SUBSET Addr, mb \in Mailboxes,
                ret_r \in Addr, ids \in SUBSET Communications, mutex \in Mutexes:
         (* \/ AsyncSend(actor, mb, data_r, comm_r)
          \/ AsyncReceive(actor, mb, data_r, comm_r)
          \/ Wait(actor, comms)
          \/ Test(actor, comms, ret_r)
          \/ Local(actor) *)
          \/ MutexAsyncLock(actor,mutex,req)
          \/ MutexWait(actor, req)
          \/ MutexTest(actor,req, test_r) 
          \/ MutexUnlock(actor,mutex)
          
 
 
        
          
          
Spec == Init /\ [][Next]_<< pc, Communications, memory, waitingQueue, Requests >>
-----------------------------------------------------------------------------------------------------------------

(* Definition of the Independence relation *)
I(A,B) == ENABLED A /\ ENABLED B => /\ A => (ENABLED B)'
                                    /\ B => (ENABLED A)'
                                    /\ A \cdot B \equiv B \cdot A

-----------------------------------------------------------------------------------------------------------------
(* ------------------------- INDEPENDENCE THEOREMS --------------------------------------------------------------*)

(* Independence theorems for Communications *)

(* AsyncSend and AsyncReceive are always independent *)
THEOREM \forall p1, p2 \in Actors: \forall mb1, mb2 \in Mailboxes: 
        \forall data1, data2, comm1, comm2 \in Addr:
        (* /\ p1 /= p2   this is not necessary  since if identical, they cannot be both enabled *)
        (* those hypothesis are not necessary since enabledness is already in the definition on independence 
          /\ ENABLED AsyncSend(p1, mb1, data1, comm1)                      
          /\ ENABLED AsyncReceive(p2, mb2, data2, comm2) 
          *)
      TRUE  =>  I(AsyncSend(p1, mb1, data1, comm1), 
              AsyncReceive(p2, mb2, data2, comm2))

(* AsyncSend and Wait are independent when they concern different communications *)
(* !!! Unsure about conditions for independence *)

THEOREM \forall p1, p2 \in Actors: \forall data, comm1, comm2 \in Addr:
        \forall mb \in Mailboxes: \exists c \in Communications:
        /\ p1 /= p2        (* p1 and p2 are different Actors *)
        /\ c.id = memory[p2][comm2]                          (*  c is the communication with id comm2 *)
        /\ \/ (p1 /= c.dst /\ p1 /= c.src)                   (*  either p1 is neither src nor dst of c *)
           \/ (comm1 /= c.data_src /\ comm1 /= c.data_dst)   (*  or     comm1 is neither src or dst addr of c *) 
        (*  /\ ENABLED AsyncSend(p1, mb, data, comm1) 
            /\ ENABLED Wait(p2, comm2) 
            *)
         =>  I(AsyncSend(p1, mb, data, comm1), 
               Wait(p2, comm2)) 

(* !!!!! Similar theorems should hold for AsyncSend and Test, AsyncReceive and Wait, AsyncReceive and Test *)
(* to be done ... *)


(* two AsyncSend are independent if they concern (different processes and) different mailboxes *)
THEOREM \forall p1, p2 \in Actors: \forall mb1, mb2 \in Mailboxes: 
        \forall data1, data2, comm1, comm2 \in Addr:
        (* /\ p1 /= p2   this is unnecessary since they would not be both enabled if equal *)
        /\ mb1 /= mb2
        (* /\ ENABLED AsyncSend(p1, mb1, data1, comm1) 
           /\ ENABLED AsyncSend(p2, mb2, data2, comm2)  
           *)
        => I(AsyncSend(p1, mb1, data1, comm1),
             AsyncSend(p2, mb2, data2, comm2))
(* two AsyncReceive are independent if thy concern (different processes and) different mailboxes *)
THEOREM \forall p1, p2 \in Actors: \forall mb1, mb2 \in Mailboxes: 
        \forall data1, data2, comm1, comm2 \in Addr:
        (* /\ p1 /= p2  *)
        /\ mb1 /= mb2
        (* /\ ENABLED AsyncReceive(p1, mb1, data1, comm1)
           /\ ENABLED AsyncReceive(p2, mb2, data2, comm2) 
           *)
        => I(AsyncReceive(p1, mb1, data1, comm1),
             AsyncReceive(p2, mb2, data2, comm2))


(* two Wait actions are always independent  *)
THEOREM \forall p1, p2 \in Actors: \forall comm1, comm2 \in Addr:
        (* /\ p1 /= p2 *)
       (* /\ comm1 = comm2
        /\ ENABLED Wait(p1, comm1)
        /\ ENABLED Wait(p2, comm2) *)
      TRUE => I(Wait(p1, comm1), Wait(p2, comm2))

(*!!!! Similar theorems should also hold for two Test actions *)
(* to be done ... *)

(* Independence Theorems for synchoronization actions *) 
(* to be done ... *)

(* Independence theorems between communication and synchronization actions *)
(* to be done ... *)

(* Independence Theorems for Local actions and all other actions *)
(* to be done ... *)


=============================================================================
\* Modification History
\* Last modified Mon Jun 11 14:07:58 CEST 2018 by diep-chi
\* Created Fri Jan 12 18:32:38 CET 2018 by diep-chi
