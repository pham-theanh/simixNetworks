----------------------------------------- MODULE networkSpecification -------------------------------------------------


(*This specification formally describes (builds the formal model of) programs/distributed systems that are simulated in SimGrid. 
    It focuses on modeling the how the global state of the system evoluates by the effect of actions: 
                   
                   current state
                        |
                        |
                        | action
                        |
                        v
                   next state 
                   
  - The state of the system is represented by 7 variables: Communications, Mailboxes, Memory, pc, Mutexes, commId and MtRequests
    + Communications is the set of all paired communications in the system (i.e. when a pair of send and receive requests have been matched) 
    + Mailboxes is an array indexed by MailboxesIds ; Mailboxes[mId] is a FIFO queue which stores send or receive requests (unpaired communications),
    + Memory is an array indexed by ActorsIds, Memory[aId] is a memory local to the actor aId used to store ids of communications, ids of MtRequests and values of local variables 
    + pc is an array indexed by ActorsIds; pc[aId] represents the program counter of the actor aId, changed  after firing each action 
    + Mutexes is an array indexed by MutexesIds; Mutexes[mId] is a FIFO queue that remembers which actors have required the mutex 
    + MtRequests is an array indexed by ActorsIds; MtRequests[aId] is the set of all the MutexesIds requested by the actor aId   
    + commId is used to set id for communications
  - Actions are structured in 3 subsystems:
    - the Local actions :  Local, 
    - the Communication actions: AsyncSend, AsyncReceive, Wait, Test,
    - the Synchronization actions: MutexAsyncLock, MutexUnLock, MutexTest and MutexWait.
   *)
   
(*---------------------------- GENERAL CONSTANTS, VARIABLES, FUNCTIONS  --------------------------------------------*)


EXTENDS Integers , Naturals, Sequences, FiniteSets, TLC   


CONSTANTS (*Sets containing the names of all the actors, mailboxes and mutexes *)
          ActorsIds, MailboxesIds, MutexesIds,
          (*Set of all existing Memory addresses. Each actor has its own private Memory, indexed by these addresses *)
          Addresses,
          (*The test action writes a boolean in Memory *)
          ValTrue, ValFalse,
          (*Existing Actions Types *)
          SendIns, ReceiveIns, WaitIns, TestIns, LocalIns,
          LockIns, UnlockIns,  MwaitIns, MtestIns
          
VARIABLES Communications, Memory, pc,  Mutexes, MtRequests, Mailboxes, commId

NoActor == CHOOSE a : a \notin ActorsIds
NoAddr == CHOOSE addr : addr \notin Addresses

ASSUME ValTrue \in Nat
ASSUME ValFalse \in Nat

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
ASSUME Partition({SendIns, ReceiveIns, WaitIns, TestIns
                 (*, LocalIns , LockIns, UnlockIns, MwaitIns, MtestIns*)}) 

Instr ==UNION {SendIns, ReceiveIns, WaitIns, TestIns
              (*, LocalIns , LockIns, UnlockIns, MwaitIns, MtestIns*)}


(* Initially there are no Communications, no MtRequests on the mutexes, Memory has random values *)

Init == /\ Communications = { }
        (*/\ Memory \in [ActorsIds -> [Addresses -> Nat]*)
        (*Set Memory for running model*)
        /\ Memory \in [ActorsIds -> [Addresses -> {0}]]
        /\ Mutexes = [i \in MutexesIds |-> <<>>] 
        /\ Mailboxes = [i \in MailboxesIds |-> <<>>] 
        /\ MtRequests = [i \in ActorsIds |-> {}]
        (*/\ pc = CHOOSE f \in [ActorsIds -> Instr] : TRUE*)
        /\ pc = [a \in ActorsIds |-> "lock"] 
        /\ commId = 0



(* Comm type is declared as a structure *)  
Comm == [id:Nat,
         status:{"send", "receive", "done"},
         src:  ActorsIds \cup { NoActor },
         dst:  ActorsIds  \cup { NoActor },
         data_src:   Addresses \cup { NoAddr },
         data_dst:  Addresses \cup { NoAddr }]

(* Invariants to check everything in the right domains*)
TypeInv == /\ \forall c \in Communications : c \in Comm /\ c.status = "done" 

           /\ \forall mbId \in MailboxesIds: ~\exists c \in DOMAIN Mailboxes[mbId]:
                         \/ Mailboxes[mbId][c] \notin Comm
                         \/ Mailboxes[mbId][c].status \notin {"send", "receive"}  
                         \/ \exists c1 \in DOMAIN Mailboxes[mbId] : Mailboxes[mbId][c].status /= Mailboxes[mbId][c1].status
                                                     
           /\ \forall mId \in MutexesIds: \forall id \in  DOMAIN Mutexes[mId]: Mutexes[mId][id] \in ActorsIds


                           (*-------------------- FUNCTIONS -------------------*)
 
                       

(*---  FUNCTIONS ON SEQUENCES USED FOR FIFO QUEUES -- *)
           
(* getIndex(e,q) gives the position of e in the sequence q *)           
getIndex(e,q) == CHOOSE n \in DOMAIN q : q[n] = e

(*isHead(m,q) checks whether m is the first element in the sequence q *)
isHead(m,q) == IF q = <<>> THEN FALSE  
                ELSE IF m = Head(q) THEN  TRUE
                     ELSE FALSE 
                     
(* Remove(e,q) removes e from sequence q*)                     
remove(e,q) == SubSeq(q, 1, getIndex(e,q)-1) \circ SubSeq(q, getIndex(e,q)+1, Len(q))
                                                               
(*isMember(m, q) checks whether m is a member of sequence q*) 
isMember(m, q) == IF \E i \in (1..Len(q)): m = q[i] THEN TRUE
                  ELSE FALSE


   
(* ---------------------------------------------------- LOCAL SUBSYSTEM ---------------------------------------------*)


(* A local computaion of Actor <aId> can change the value of this Actor's Memory at any address *)

Local(aId) ==
    /\ aId \in ActorsIds
    /\ pc[aId] \in LocalIns
    \*change value of Memory[aId][a], set {0,1,2,3,4,5} just for running model
    /\ Memory' \in [ActorsIds -> [Addresses -> {0,1,2,3,4,5}]]
    /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
    /\ UNCHANGED <<Communications, Mutexes, MtRequests, Mailboxes, commId >>


(* ---------------------------------------------COMMUNICATION SUBSYSTEM -----------------------------------*)

(* AsyncSend(aId,mbId,data_addr,comm_addr):  
    the actor <aId> sends a "send" request to the mailbox <mbId>. 
    If a pending "receive" request already exists, they are combined to create a "done" paired communication in Communications and
    data is copied from the source to the destination 
    otherwise a new communication with "send" status is created,
    address <data_addr> of Actor <aId> contains the data to transmit,
    and Memory address <comm_addr> of Actor <aId> is assigned the id of the communication 

  Parameters:
    - aId: the ActorsIds of the sender 
    - mbId: the MailboxesIds where the "send" communication request is pushed 
    - data_addr: the address in the AsyncSender's Memory where the data to transmit is stored 
    - comm_addr: the address in the AsyncSender's Memory where to store the communication id *)
 
AsyncSend(aId, mbId, data_addr, comm_addr) == 
  /\ aId \in ActorsIds
  /\ mbId\in MailboxesIds
  /\ data_addr \in Addresses
  /\ comm_addr \in Addresses
  /\ pc[aId] \in SendIns
        (*If the maibox is empty or contains only send communications, create a "send" 
                                                             communication in the mailbox *)
  /\ \/ /\ \/  Len(Mailboxes[mbId]) = 0
           \/ /\ Len(Mailboxes[mbId]) > 0 
              /\ Head(Mailboxes[mbId]).status = "send" 
        /\ LET comm ==  
                 [id |-> commId, 
                  status |-> "send", 
                  src |-> aId,
                  dst |-> NoActor, 
                  data_src |-> data_addr,
                  data_dst |-> NoAddr]
            IN
                /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Append(Mailboxes[mbId],comm)]
                /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id] 
                /\ UNCHANGED <<Communications>>    
                /\ commId' = commId+1
                
        (*Else the mailbox is not empty *)
     \/ /\ Len(Mailboxes[mbId]) >  0
        /\ Head(Mailboxes[mbId]).status = "receive"    
        /\ LET comm == Head(Mailboxes[mbId])
                (*If a matching "receive" request exists in the Mailboxes(mbId), choose the oldest one and
                    complete the Sender fields, set the communication to the "done" state and copy the data*)
           IN \/ /\ Communications' = 
                     Communications \cup {[comm EXCEPT
                                       !.status = "done",
                                       !.src = aId,
                                       !.data_src = data_addr]}
                 /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Tail(Mailboxes[mbId])]
                 /\ Memory' = [Memory EXCEPT ![comm.dst][comm.data_dst] = 
                                                    Memory[aId][data_addr]]
                 /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id] 
                 /\ UNCHANGED <<commId>>
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
  /\ UNCHANGED << Mutexes, MtRequests>> 

(* AsyncReceive(aId,mbId,data_addr,comm_addr): the actor <aId> sends a "receive" request to the mailbox <mbId>.
   If there is a pending "send" request on the same mailbox <mbId>, they are combined to create a "done" paired 
   communication in Communications and data is coppied from the source to the destination, 
   otherwise a new communication is created with "receive" status.
   the address <data_addr> 
   the address <comm_addr> of <aId> is assigned the id of the communication,
   
  Parameters: 
    - aId: the Actor ID of the receiver 
    - mbId: the mailbox where the "receive" communication request is going to be pushed 
    - data_addr: the address in the receivers's Memory where the data is going to be stored 
    - comm_addr: the address in the receivers's Memory where to store the communication id *)
    
AsyncReceive(aId, mbId, data_addr, comm_addr) == 
  /\ aId \in ActorsIds
  /\ mbId\in MailboxesIds
  /\ data_addr \in Addresses
  /\ comm_addr \in Addresses
  /\ pc[aId] \in ReceiveIns
    (*If the maibox is empty or contains only "receive" communications, create a "receive" 
                                                                    communication in the mailbox *)
  /\ \/ /\ \/ Len(Mailboxes[mbId]) = 0
           \/ /\ Len(Mailboxes[mbId]) > 0 
              /\ Head(Mailboxes[mbId]).status = "receive"
        /\ LET comm ==  
                 [id |-> commId,
                  status |-> "receive", 
                  src |-> NoActor,
                  dst |-> aId, 
                  data_src |-> NoAddr,
                  data_dst |-> data_addr]
           IN
             /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Append(Mailboxes[mbId], comm)]
             /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id]
             /\ UNCHANGED <<Communications>>    
             /\ commId' = commId+1
            (*Else the mailbox is not empty *)
     \/ /\ Len(Mailboxes[mbId]) >  0
        /\ Head(Mailboxes[mbId]).status = "send"     
        /\ LET comm == Head(Mailboxes[mbId]) 
           (* If a matching "send" request exists in the mailbox mbId, choose the oldest one and,
            complete the receiver's fields and set the communication to the "done" state *)
           IN \/ /\ Communications' = 
                    Communications \cup {[comm EXCEPT
                                       !.status = "done",
                                       !.dst = aId,
                                       !.data_dst = data_addr
                                        ]}
                 /\ Memory' = [Memory EXCEPT ![aId][data_addr] = 
                                                    Memory[comm.src][comm.data_src]]
                 /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Tail(Mailboxes[mbId])]
                 /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id]
                 /\ UNCHANGED <<commId>>
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests >> 

(* Wait(aId,comm_addrs):  Actor <aId> waits for at least one communication from a given set <comm_addrs> to complete 
    If it is already "done", there is nothing to do.
    Else the function is blocking when no communication is "done".   
 Parameters:
    - aId: the Actor's ID issuing the wait request
    - comm_addrs: the list of addresses in the Actor's Memory where the communication ids are stored 
*)

WaitAny(aId, comm_addrs) ==
  /\ aId \in ActorsIds
  /\ pc[aId] \in WaitIns
  /\ \E comm_addr \in comm_addrs, c \in Communications: c.id = Memory[aId][comm_addr]
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests, Mailboxes, commId, Memory, Communications >>
 (* otherwise i.e. no communication in <comm_addrs> is  "done", WaitAny is blocking *)


(* Test(aId, comm_addrs, testResult_Addr): Actor <aId> waits for at least one communication from a given list <comm_addrs> to complete,
    and returns the boolean result at Memory adress <testResult_Addr>.
    The function is very similar to Wait, but returns a boolean value as a result, and is never blocking.
    Parameters
    - aId: the Actor ID issuing the test request 
    - comm_addrs: the list of addresses in the Actor's Memory where the communication ids are stored 
    - testResult_Addr: the address in the Actor Memory where the boolean result is going to be stored *)
    

TestAny(aId, comm_addrs, testResult_Addr) ==
  /\ aId \in ActorsIds
  /\ testResult_Addr \in Addresses
  /\ pc[aId] \in TestIns
  /\ \/ \E comm_addr \in comm_addrs, comm \in Communications: comm.id = Memory[aId][comm_addr] /\
        (* If the communication is "done" return ValTrue *)
           /\ comm.status = "done"
           /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = ValTrue]
        (* if no communication is "done", return ValFalse *)   
     \/ /\ ~ \exists comm_addr \in comm_addrs, comm \in Communications: comm.id = Memory[aId][comm_addr]
                /\ comm.status = "done"
        /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = ValFalse]
  (* Test is non-blocking since in all cases pc[aId] is incremented *)
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests, Mailboxes,Communications, commId>>
  

(* -------------------------------- SYNCHRONIZATION SUBSYSTEM ----------------------------------------------------*)
                                
(* MutexAsyncLock(aId, mid, req_a) : Actor <aId> is requesting a lock on mutex <mid>. If allowed, address <req_a> stores the mutex id <mid>.    
- If the actor <aId> has no pending request on mutex <mid>, a new one is created 
        - add pair [mid,req_a] in Request[aId]
        - store <mid> in Memory[aId][req_a], i.e. local address <req_a> is assigned value <mid>
        - enqueue <aId> in Mutexes[mid]
 The operation is non-blocking (pc[aId] is modified in any case)       
*) 
 
 
 MutexAsyncLock(aId, mId, req_addr) ==
   /\ aId \in ActorsIds
   /\ pc[aId] \in LockIns
   /\ mId \in MutexesIds
   /\ req_addr \in Addresses
         (* if Actor <aId> has no pending request on mutex <mid>, create a new one *)      
   /\ \/ /\ ~isMember(aId, Mutexes[mId])
         /\  MtRequests'  = [MtRequests EXCEPT ![aId]= MtRequests[aId] \cup {mId}]
         /\  Memory' = [Memory EXCEPT ![aId][req_addr] = mId]  
         /\  Mutexes' = [Mutexes EXCEPT ![mId] = Append(Mutexes[mId], aId)]
         (* otherwise i.e. actor <aId> alreadly has a pending request on mutex <mid>, keep the variables unchanged *)          
      \/ /\ isMember(aId, Mutexes[mId]) 
         /\ UNCHANGED <<Mutexes,  Memory, MtRequests>>  
   (* MutexAsyncLock is never blocking, in any case, pc[aId] is incremented *) 
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
   /\ UNCHANGED <<Communications, Mailboxes, commId>>
       
  
  
(* MutexUnlock(aId, mId): the Actor <aId> wants to release the mutex <mid>
    - it is either a normal unlock when <aId> owns <mid> (it is head of Mutexes[mid]) 
    - or a cancel otherwise. 
    In both cases all links between <mid> and <aId> are removed in Mutexes[mid] and MtRequests[aId] 
 *)
 
MutexUnlock(aId, req_addr) ==
   /\ aId \in ActorsIds
   /\ req_addr \in Addresses
   /\ pc[aId] \in UnlockIns
   /\ Mutexes' = [Mutexes EXCEPT ![Memory[aId][req_addr]] = remove(aId,Mutexes[Memory[aId][req_addr]])]
   /\ MtRequests' = [MtRequests EXCEPT ![aId] = MtRequests[aId] \ {Memory[aId][req_addr] }]
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
   /\ UNCHANGED <<Memory, Communications, Mailboxes, commId>>
   
   (* Otherwise, the transition is not enabled and Actor <aId> is blocked *)
   
   
(* MutexWait(aId, req_addr): Actor <aId> waits for a lock request whose id is store in <req_addr>, 
  - if there is a req in MtRequests[aId] whose mid is store in  <req_addr>, and <aId> is the owner of this mutex mid (head of Mutexes[req.id]), 
    then MutexWait is enabled
  - otherwise the transition is not enabled.
  MutexWait is thus blocking until <aId> owns the mutex 
 *)


(*
MutexWait(aId, req_addr) == 
/\ aId \in ActorsIds
/\ req_addr \in Addresses
/\ pc[aId] \in MwaitIns
    (* If req_a is the id of a Request of Actor <aId>, and <aId> is the owner of this mutex, <aId> proceeds and increment its pc *) 
/\ \E req \in MtRequests[aId]: req = Memory[aId][req_addr] /\ isHead(aId, Mutexes[req])
/\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
/\ UNCHANGED << Memory, Mutexes, MtRequests, Communications, Mailboxes, commId>>
*)


MutexWait(aId, req_addrs) ==
  /\ aId \in ActorsIds
  /\ pc[aId] \in MwaitIns
  /\ \E req_add \in req_addrs, req \in MtRequests[aId]: req = Memory[aId][req_add] /\ isHead(aId, Mutexes[req])
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
  /\ UNCHANGED << Memory, Mutexes, MtRequests, Communications, Mailboxes, commId>>

(* otherwise <aId> is blocked, pc[aId] is unmodified *)  


(* MutexTest(aId, req_addrs, testResult_Addr): actor <aId> tests if he is the owner of some mutex whose id is store in <req_addr>
            (i.e. he is the head of the mutex Mutexes)
            and stores the boolean result at address <testResult_Addr> 
            MutexTest is non-blocking (in any case pc[aId] is modified).
            *)

MutexTest(aId, req_addrs, testResult_Addr) ==
  /\ aId \in ActorsIds
  /\ pc[aId] \in MtestIns
  /\ testResult_Addr \in Addresses
  /\ \/ \E req_add \in req_addrs, req \in  MtRequests[aId]: req = Memory[aId][req_add]/\ 
     (* If the actor is the owner of some mutex then return true *)
        \/ /\ isHead(aId, Mutexes[req])
           /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = ValTrue]
     
     (*Else it is not the owner of any mutex then return false *)
     \/ /\~\E req_add \in req_addrs, req \in  MtRequests[aId]: req = Memory[aId][req_add]/\    
           /\ isHead(aId, Mutexes[req])
        /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = ValFalse]
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![aId] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests, Communications,  Mailboxes, commId>>


--------------------------------------------------------------------------------------------------------------------------------
                                    (*INDICATE NEXT ACTIONS *)
                                    
(* Next indicates the possible actions that could be fired at a state  *)
Next == \exists actor \in ActorsIds, mbId\in MailboxesIds, mutex \in MutexesIds, data_addr,
        comm_addr, req_addr, result_addr \in Addresses, req_addrs, comm_addrs \in SUBSET Addresses:
                
          \/ AsyncSend(actor, mbId, data_addr, comm_addr)
          \/ AsyncReceive(actor, mbId, data_addr, comm_addr)
          \/ WaitAny(actor, comm_addrs)
          \/ TestAny(actor, comm_addrs, result_addr)
          \/ Local(actor) 
          \/ MutexAsyncLock(actor, mutex, req_addr)
          \/ MutexWait(actor, req_addrs)
          \/ MutexTest(actor,req_addrs, result_addr) 
          \/ MutexUnlock(actor, req_addr)
          

Spec == Init /\ [][Next]_<< pc, Communications, Memory, Mutexes, MtRequests, Mailboxes, commId >>
-----------------------------------------------------------------------------------------------------------------

(* Definition of the Independence relation *)

           (*Executing A does not enable or disable B*) 
I(A,B) == /\ ENABLED A =>   /\ ENABLED B => (A => (ENABLED B)')
                            /\ (A => (ENABLED B)') =>  ENABLED B 
           (*if both A and B are enabled, their execution can be commuted*)
          /\ (ENABLED  A /\ ENABLED B)  => /\ A => (ENABLED B)'
                                           /\ B => (ENABLED A)'
                                           /\ A \cdot B \equiv B \cdot A

-----------------------------------------------------------------------------------------------------------------
(* ------------------------------------------ INDEPENDENCE THEOREMS-----------------------------------------------------*)

(* Independence theorems for Communications *)

 (*A LocalComputation action is independent with all other actions*)
 THEOREM \forall a1, a2 \in ActorsIds, mt \in MutexesIds, req,  data, comm, test_r \in Addresses,
         mbId\in MailboxesIds, comm_addrs \in SUBSET Addresses:
           a1 /= a2 =>
           /\ I(Local(a1), AsyncSend(a2, mbId, data, comm))
           /\ I(Local(a1), AsyncReceive(a2, mbId, data, comm))  
           /\ I(Local(a1), WaitAny(a2, comm_addrs))   
           /\ I(Local(a1), TestAny(a2, comm_addrs, test_r))   
           /\ I(Local(a1), MutexWait(a2, req))
           /\ I(Local(a1), MutexTest(a2, req, test_r))
           /\ I(Local(a1), MutexUnlock(a2, mt))
           /\ I(Local(a1), MutexUnlock(a2, mt))
 
 (*A synchoronization action (MutexAsyncLock, MutexUnlock, MutexWait, MutexTest) is independent with 
 a communication action (AsyncSend, AsyncReceive, TestAny, WaitAny) if they are performed by different actors*)
 
THEOREM \forall a1, a2 \in ActorsIds, mt \in MutexesIds, req,  data, comm, test_r1,  test_r2 \in Addresses,
         mbId\in MailboxesIds, comm_addrs \in SUBSET Addresses:
           a1 /= a2 =>
           /\ I(MutexAsyncLock(a1, mt, req), AsyncSend(a2, mbId, data, comm))
           /\ I(MutexAsyncLock(a1, mt, req), AsyncReceive(a2, mbId, data, comm))  
           /\ I(MutexAsyncLock(a1, mt, req), WaitAny(a2, comm_addrs))   
           /\ I(MutexAsyncLock(a1, mt, req), TestAny(a2, comm_addrs, test_r1))   
           
           /\ I(MutexUnlock(a1, mt), AsyncSend(a2, mbId, data, comm))
           /\ I(MutexUnlock(a1, mt), AsyncReceive(a2, mbId, data, comm))  
           /\ I(MutexUnlock(a1, mt), WaitAny(a2, comm_addrs))   
           /\ I(MutexUnlock(a1, mt), TestAny(a2, comm_addrs, test_r1))
              
           /\ I(MutexWait(a1, req), AsyncSend(a2, mbId, data, comm))
           /\ I(MutexWait(a1, req), AsyncReceive(a2, mbId, data, comm))
           /\ I(MutexWait(a1, req), WaitAny(a2, comm_addrs))
           /\ I(MutexWait(a1, req), TestAny(a2, comm_addrs, test_r1))
          
           /\ I(MutexTest(a1, req, test_r1), AsyncSend(a2, mbId, data, comm))
           /\ I(MutexTest(a1, req, test_r1), AsyncReceive(a2, mbId, data, comm))
           /\ I(MutexTest(a1, req, test_r1), WaitAny(a2, comm_addrs))   
           /\ I(MutexTest(a1, req, test_r1), TestAny(a2, comm_addrs, test_r2))   
           


(* two AsyncSend  or two AsyncReceive are independent if they concern different mailboxes 
THEOREM \forall a1, a2 \in ActorsIds, mbId1, mbId2 \in MailboxesIds, data1, data2, comm1, comm2 \in Addresses:
        /\ a1 /= a2 
        /\ mbId1 /= mbId2
  
         => /\ I(AsyncSend(a1, mbId1, data1, comm1), AsyncSend(a2, mbId2, data2, comm2)) 
            /\ I(AsyncReceive(a1, mbId1, data1, comm1),  AsyncReceive(a2, mbId2, data2, comm2))
*)

(* two communication actions are independent if they concern different mailboxes
   *)
THEOREM \forall a1, a2 \in ActorsIds, mbId1, mbId2 \in MailboxesIds, data1, data2, comm1, comm2 \in Addresses:
        /\ a1 /= a2 
        /\ mbId1 /= mbId2
  
         => /\ I(AsyncSend(a1, mbId1, data1, comm1), AsyncSend(a2, mbId2, data2, comm2)) 
            /\ I(AsyncReceive(a1, mbId1, data1, comm1),  AsyncReceive(a2, mbId2, data2, comm2))
            /\ I(AsyncSend(a1, mbId1, data1, comm1), AsyncReceive(a2, mbId2, data2, comm2)) 




(* AsyncSend and AsyncReceive are always independent *)

THEOREM \forall a1, a2 \in ActorsIds, mbId1, mbId2 \in MailboxesIds, data1, data2, comm1, comm2 \in Addresses:
           a1 /= a2 => 
           I(AsyncSend(a1, mbId1, data1, comm1), AsyncReceive(a2, mbId2, data2, comm2))
       
(* two WaitAny actions, or two TestAny actions, or a WaitAny action and a TestAny are independent*)
THEOREM \forall a1, a2 \in ActorsIds, comm_addrs1, comm_addrs2 \in SUBSET Addresses, test_r1, test_r2 \in Addresses:
        a1 /= a2 => 
           /\ I(WaitAny(a1, comm_addrs1), WaitAny(a2, comm_addrs2))
           /\ I(TestAny(a1, comm_addrs1, test_r1), TestAny(a2, comm_addrs2, test_r2))   
           /\ I(WaitAny(a1, comm_addrs1), TestAny(a2, comm_addrs2, test_r2))
  

(* A WaitAny action or a TestAny action and a AsyncSend action or a 
AsyncReceive action are independent if they concern different communication. *)
(* !!! Unsure about conditions for independence *)

THEOREM \forall a1, a2 \in ActorsIds, data, comm1, comm2, test_r \in Addresses, mbId\in MailboxesIds:
              /\ a1 /= a2
              /\ Memory[a1][comm1] /=   Memory[a2][comm2]
                 =>  /\ I( WaitAny(a1, {comm1}), AsyncSend(a2, mbId, data, comm2)) 
                     /\ I( WaitAny(a1, {comm1}), AsyncReceive(a2, mbId, data, comm2)) 
                     /\ I(TestAny(a1, {comm1}, test_r ), AsyncSend(a2, mbId, data, comm2))
                     /\ I( TestAny(a1, {comm1}, test_r ), AsyncReceive(a2, mbId, data, comm2))  


(*Two synchronization actions are independent if they concern different mutexes and performed by different actors.*)
THEOREM \forall a1, a2 \in ActorsIds, mt1, mt2 \in MutexesIds, req1, req2, test_r \in Addresses:
        /\ a1 /= a2
        /\ mt1 /= mt2
        /\ Memory[a2][req1] /= mt1
        => /\ I(MutexAsyncLock(a1, mt1, req1), MutexAsyncLock(a2, mt2, req2))
           /\ I(MutexAsyncLock(a1, mt1, req1), MutexUnlock(a2, mt2))
           /\ I(MutexUnlock(a1, mt2), MutexUnlock(a2, mt2))
           /\ I(MutexAsyncLock(a1, mt1, req1), MutexTest(a2, req2, test_r))      
           /\ I(MutexAsyncLock(a1, mt1, req1), MutexWait(a2, req1))      
           /\ I(MutexUnlock(a1, mt1), MutexUnlock(a2, mt2))
           /\ I(MutexUnlock(a1, mt1), MutexWait(a2, req1))
           /\ I(MutexUnlock(a1, mt1), MutexTest(a2, req1, test_r))

(* MutexAsyncLock actions and MutexUnlock action are independent*)
 
THEOREM \forall a1, a2 \in ActorsIds, mt1, mt2 \in MutexesIds, req1, req2 \in Addresses:
        /\ a1 /= a2 =>  I(MutexAsyncLock(a1, mt1, req1), MutexUnlock(a2, req2))

      
 (*Two MutexWait actions, two MutexTest actions, a MutexWait action and MutexTest action are independent*)             
THEOREM \forall a1, a2 \in ActorsIds, mt1, mt2 \in MutexesIds, req1, req2, test_r1, test_r2 \in Addresses,  
           comm_addrs1 , comm_addrs2 \in SUBSET Addresses:
           a1 /= a2 => 
           /\ I(MutexWait(a1, req1), MutexWait(a2, req2))
           /\ I(MutexWait(a1, req1), MutexTest(a2, req1, test_r1))
           /\ I(MutexTest(a1, req1, test_r1), MutexTest(a2, req2, test_r2))
           
 (* A MutexAsyncLock action and a MutexWait action or MutexTest action are independent*)
 THEOREM \forall a1, a2 \in ActorsIds, mt \in MutexesIds, req1, req2, test_r \in Addresses:
         a1 /= a2 =>
         /\ I(MutexAsyncLock(a1, mt, req1), MutexWait(a2, req2))
         /\ I(MutexAsyncLock(a1, mt, req1), MutexTest(a1, req2, test_r))

 (* A MutexUnlock action and a MutexWait action or MutexTest action are independent if concern different mutexes*)
THEOREM \forall a1, a2 \in ActorsIds, mt \in MutexesIds, test_r, req, req1 \in Addresses:
            /\ a1 /= a2 
            /\ Memory[a1][req] /= mt => /\ I(MutexUnlock(a1, req1), MutexWait(a2, req))
                                        /\ I(MutexUnlock(a1, req1), MutexTest(a2, req, test_r))


(*A \mutexunlock~is independent of a \mutexwait~or \mutextest~of another actor, 
except if they concern the same mutex and one of the actors owns the mutex  ??? *)

 
 
=============================================================================
\* Modification History
\* Last modified Mon Feb 11 14:23:19 CET 2019 by diep-chi
\* Created Fri Jan 12 18:32:38 CET 2018 by diep-chi
