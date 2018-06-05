----------------------------------------- MODULE networkSpecification -------------------------------------------------


(* This specification formally describes (build formal model of) programs/system that are simulated in SimGrid, 
    it focus on modeling the states and actions of the system, firing an action at a current state leads to a next state
                   
                   current state
                        |
                        |
                        | action
                        |
                        v
                   next state 
                   
  - A state is represented by 4 variables: Communications, memory, pc, waitingQueue and Requests
    + Communications is used to store all communications in the system
    + memory  that is indexed by id of Actors stores id of communications, id of requests
    + pc is indexed by id of Actors, presents program counter of actors, each time after firing one action the pc change to pc' 
    + each mutex[mid] in the model has a waitinQueue[mid] that hepls the mutex remember which actors have require on it
    + each actor[Aid] has a Requests[Aid] including all the id of mutexes required by the actor   
   
  - There are 9 actions: AsyncSend, AsyncReceive, Wait, Test, Local, MutexAsyncLock, MutexUnLock, MutexTest and MutexWait.
    An action can use funtions that are defined before it for computations. 
   *)
   
(*-----------------------------------DECLARE VARIABLES, CONSTANTS FOR BUILDING AND RUNNING MODEL--------------------------------*)
    
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANTS Mailboxes, Addr, Actors, Mutexes, ValTrue, ValFalse, SendIns, ReceiveIns, WaitIns, 
          TestIns, LocalIns, LockIns, UnlockIns,  MwaitIns, MtestIns
          
VARIABLES Communications, memory, pc, waitingQueue, Requests

NoActor == CHOOSE p : p \notin Actors
NoAddr == CHOOSE a : a \notin Addr

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
Instr ==UNION {SendIns, ReceiveIns, WaitIns, TestIns, LocalIns ,LockIns, UnlockIns, MwaitIns, MtestIns}


ASSUME Partition({SendIns, ReceiveIns, WaitIns, TestIns, LocalIns , LockIns, UnlockIns, MwaitIns, MtestIns}) 


ASSUME ValTrue \in Nat
ASSUME ValFalse \in Nat


Comm == [id:Nat,
         mb:Mailboxes,
         status:{"send","receive","ready","done"},
         src:Actors,
         dst:Actors,
         data_src:Addr,
         data_dst:Addr]
------------------------------------------------------------------------------------------------------------
                               (*DEFINE 4 FUNCTIONS THAT WILL BE USED IN THE ACTIONS*)
           
(* getIndex(e,q) gives the position of e in sequence q *)           

getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e


(*isHead(m,q) checks whether m is the first element in the sequence q? *)

isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 
                     
(* Remove(e,q) removes e from q*) 
                    
Remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))
                     
                     
                     
(*isMember(m, q) check whether m is the member in set q*) 
 
isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE

    

----------------------------------------------------------------------------------------------------------------

(* Let's keep everything in the right domains, just for checking *)
TypeInv == /\ Communications \subseteq Comm
           /\ memory \in [Actors -> [Addr -> Nat]]
           /\ pc \in [Actors -> Instr]




------------------------------------------------------------------------------------------------------------------
(* Two following variables: maibox, CommBuffers are updated aumatically each time after fring transitions*)


(*mailbox(mb) is a maibox including all pending request posted on it*)
mailbox(mb) == {comm \in Communications : comm.mb=mb /\ comm.status \in {"send","receive"}}


(* The set of memory addresses of a Actor being used in a communication *)
CommBuffers(Aid) == 
  {c.data_src: c \in { y \in Communications: y.status /= "done" /\ (y.src = Aid \/ y.dst = Aid)}} 
\cup {c.data_dst: c \in { y \in Communications: y.status /= "done" /\ (y.src = Aid \/ y.dst = Aid)}} 
\cup {req.add : req \in Requests[Aid]}


------------------------------------------------------------------------------------------------------------------
                                            (*DEFINE THE COMMUNICATION ACTIONS*)

(*AsyncSend sends a "send" request by actor Aid to the maibox mb. If there is a pending "receive" request, they are combined
  to create a ready communication in the set Communications, the id of the request will be strore in memory comm_r*)
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
  /\ UNCHANGED <<  waitingQueue,Requests>>
  
 
 
 
 
(*AsyncReceive sends a "receive" request by actor Aid to the maibox mb.
 If there is a pending "send" request, they are combined to create a ready communication,
 the id of the communication will be strore in memory of actor Aid at comm_r address*)
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
  /\ UNCHANGED <<waitingQueue,Requests>>




(* Wait for at least one communication from a given list to complete*)
(* If the communication is ready for being processed, data is transfered from the source actor to the destination actor *)
(* Aid: the Actor's ID issuing the wait *)
(* comms: the list of addresses in the Actor's memory where the communication ids are stored *)


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
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests>>






(* Test if at least one communication from a given list has completed *)
(* Aid: the Actoress ID issuing the wait *)
(* comms: the list of addresses in the Actoress's memory where the communication ids are stored *)
(* ret_r: the address in the Actoress's memory where the result is going to be stored *)
Test(Aid, comms, ret_r) ==
  /\ ret_r \in Addr
  /\ Aid \in Actors
  /\ pc[Aid] \in TestIns
  /\ \/ \E comm_r \in comms, c\in Communications: c.id = memory[Aid][comm_r] /\
        (* If the communication is "ready" the data is transfered*)
        \/ /\ c.status = "ready"
           /\ memory' = [memory EXCEPT ![c.dst][c.data_dst] = memory[c.src][c.data_src],
                                        ![Aid][ret_r] = ValTrue]
           /\ Communications' = (Communications \ {c}) \cup {[c EXCEPT !.status = "done"]}
        (* else if the cummunication is already done, keep Communications unchanged*)   
        \/ /\ c.status = "done"
           /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValTrue]
           /\ UNCHANGED <<Communications>>
           
           
     \/ ~ \exists comm_r \in comms, c \in Communications: c.id = memory[Aid][comm_r]
        /\ c.status \in {"ready","done"}
        /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValFalse]
        /\ UNCHANGED <<Communications>> 
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests>>
  
  
  
  
  
(* A local computaion can change value of an actor's memory at any address, but not where communication's ids are strored *)

Local(Aid) ==
    /\ Aid \in Actors
    /\ pc[Aid] \in LocalIns
    
    (*change value of memory[Aid][a]*)
    /\ memory' \in [Actors -> [Addr -> {0,1,2,3,4,5}]]
    /\ \forall p \in Actors, a \in Addr: memory'[p][a] /= memory[p][a]
    (* ensure that memory[Aid][a] is not where actor Aid strores communication *)
       => p = Aid /\ a \notin CommBuffers(Aid)
    /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
    /\ UNCHANGED <<Communications, waitingQueue,Requests>>
    
    
------------------------------------------------------------------------------------------------------------------------------
                                        (* DEFINE SYNCHRONIZATION ACTIONS*)
                                
(* When an Actor execute a Lock on a mutex:
- If the actor has a pending request on the mutex, it can not create a new request on the mutex
- else :   
    +Create a request, adding it in actor's request set
    +Store id (id of mutex) of the request in the memory 
*) 

  
  MutexAsyncLock(Aid, mid, req_a) ==
   /\ Aid \in Actors
   /\ pc[Aid] \in LockIns
   /\ mid \in Mutexes
   /\ req_a \in Addr
   (* if actor Aid currently has not a request on the mutex mid then create a request,
      and use id of mutex (mid) as the id of the request   *)
   /\ \/ /\ ~isMember(Aid, waitingQueue[mid])
         /\ LET req == 
                        [id |-> mid,
                         add |-> req_a ]
            IN /\  Requests'  = [Requests EXCEPT ![Aid]= Requests[Aid] \cup {req}]
               /\  memory' = [memory EXCEPT ![Aid][req_a] = mid]  
               /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Append(waitingQueue[mid], Aid)]
     (*if the actor Aid alreadly has a request on the mutex mid, do not create a new request, keep the variables unchanged *)          
      \/ /\ isMember(Aid, waitingQueue[mid]) 
         /\ UNCHANGED <<waitingQueue,  memory, Requests>>  
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   /\ UNCHANGED <<Communications>>
    
  
  
(* When a Actoress <Aid> does a valid unlock() on Mutex <mid>, then:
 * - If <Aid> is the owner (head of waitingQueue), that's a naive unlock and we 
 *     remove all linking between Aid and mid that was created in MutexAsyncLock.
 * - If <Aid> is not the owner, that's a cancel, and we remove the linking anyway.
 *
 * - If <Aid> is not in the waitingQueue (it did not ask for the <mid> previously),
 *   that's not enabled, and <Aid> is blocked.
 *)
 
MutexUnlock(Aid, mid) ==
   /\ Aid \in Actors
   /\ mid \in Mutexes
   /\ pc[Aid] \in UnlockIns
   
   (* If the request was previously posted (either owner or not) remove any linking *)
   /\ isMember(Aid, waitingQueue[mid]) 
   /\ waitingQueue' = [waitingQueue EXCEPT ![mid] = Remove(Aid,waitingQueue[mid])]
   /\ Requests' = [Requests EXCEPT ![Aid] = Requests[Aid] \ {CHOOSE req \in Requests[Aid] : req.id = mid }]
   (* If not a member, the transition is not enabled *)
   /\ UNCHANGED <<memory, Communications>>
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   
 
   
(* When Actor <Aid> does a mutex_wait on <mid>, 
 *  - If <Aid> is the owner of <mid>, then MutexWait is fined
 *  - ele the transition is not enabled
 *)

MutexWait(Aid, req_a) == 
/\ Aid \in Actors
/\ req_a \in Addr
/\ pc[Aid] \in MwaitIns
/\ \E req \in Requests[Aid]: req.id = memory[Aid][req_a] /\ isHead(Aid, waitingQueue[req.id])
/\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
/\ UNCHANGED << memory, waitingQueue, Requests, Communications>>



(*Test whether an actor is the owner of the mutex ( actor's id is the fist in the mutex waiting queue) *)

MutexTest(Aid, req_a,test_r) ==
  /\ Aid \in Actors
  /\ pc[Aid] \in MtestIns
  /\ test_r \in Addr
  /\  \E req \in  Requests[Aid]: req .id= memory[Aid][req_a]/\ 
       (* If the actor is the owner then return true, strore true value in memory*)
        \/ /\ isHead(Aid,waitingQueue[req.id])
           /\ memory' = [memory EXCEPT ![Aid][test_r] = ValTrue]
       (*else if it is not the onwer then return false, strore true value in memory*)
        \/ /\ ~isHead(Aid, waitingQueue[req.id])
           /\ memory' = [memory EXCEPT ![Aid][test_r] = ValFalse] 
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<waitingQueue, Requests, Communications>>
  
--------------------------------------------------------------------------------------------------------------------------------
                                    (*SET INITIAL VALUES FOR THE VARIABLES, INDICATE NEXT ACTIONS*)
                                    
                                    
(* Initially there are no messages in the Communications, no requires on the mutexes-> no Actors are waiting for mutexes, 
memory has rondom values *)

Init == /\ Communications = {}
        (*/\ memory \in [Actors -> [Addr -> Nat]*)
        
        (*Set memory for running model*)
        /\ memory \in [Actors -> [Addr -> {0}]]
        
        /\ waitingQueue = [i \in Mutexes |-> <<>>] 
        /\ Requests = [i \in Actors |-> {}]
        (*/\ pc = CHOOSE f \in [Actors -> Instr] : TRUE*)
        /\ pc = [a \in Actors |-> "lock"] 
        
        
(* indicate posible actions could be fined at a state  *)

Next == \exists actor \in Actors, data_r \in Addr, comm_r \in Addr, req \in Addr, test_r \in Addr, comms \in SUBSET Addr, mb \in Mailboxes,
                ret_r \in Addr, ids \in SUBSET Communications, mutex \in Mutexes:
          \/ AsyncSend(actor, mb, data_r, comm_r)
          \/ AsyncReceive(actor, mb, data_r, comm_r)
          \/ Wait(actor, comms)
          \/ Test(actor, comms, ret_r)
          \/ Local(actor)
          \/ MutexAsyncLock(actor,mutex,req)
          \/ MutexWait(actor, req)
          \/ MutexTest(actor,req, test_r) 
          \/ MutexUnlock(actor,mutex) 
          
 
 
        
          
          
Spec == Init /\ [][Next]_<< pc, Communications, memory, waitingQueue, Requests >>
-----------------------------------------------------------------------------------------------------------------

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


(*Independence Theorems that are relalated to synchoronization primitives are presented here    *)
=============================================================================
\* Modification History
\* Last modified Tue Jun 05 18:39:37 CEST 2018 by diep-chi
\* Created Fri Jan 12 18:32:38 CET 2018 by diep-chi
