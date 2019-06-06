--------------------------- MODULE abstractModel ---------------------------
(*THIS VERSION THERE IS NO COMMUNICATIONS IDS, JUST FOR RUNNING THE MODEL*)

(* This specification builds the formal model of programs and distributed systems that are simulated in SimGrid. 
   It focuses on modeling the how the global state of the system evoluates by the effect of actions.

  - The problem instance is specified by several constants:
    + Addresses: all existing addresses (on each actor, memory is not shared)
    + Mailboxes: All existing mailboxes in the networking subsystem (shared)
    + Mutexes: All existing mutexes in the synchronization subsystem (shared)
                   
  - The state of the system is represented by several variables:
    + doneCommunications is the set of all paired doneCommunications in the system (i.e. when a pair of send and receive requests have been matched) 
    + Mailboxes is an array indexed by MailboxesIds ; Mailboxes[mId] is a FIFO queue which stores send or receive requests (unpaired doneCommunications),
    + Memory is an array indexed by Actors, Memory[aId] is a memory local to the actor aId used to store ids of doneCommunications, ids of Locks and values of local variables 
    + Mutex is an array indexed by Mutexes; Mutex[mId] is a FIFO queue that remembers which actors have required the mutex 
    + Locks is an array indexed by Actors; Locks[aId] is the set of all the MutexesIds requested by the actor aId
    + AsyncCount is the total amount of asynchronous requests (be it comm or locks), used to constraint the exploration to small instances
  - Actions are structured in 3 subsystems:
    - the Local actions :  Local, 
    - the Communication actions: AsyncSend, AsyncReceive, Wait, Test,
    - the Synchronization actions: MutexAsyncLock, MutexUnLock, MutexTestAny and MutexWaitAny.
   *)
   
(*---------------------------- GENERAL CONSTANTS, VARIABLES, FUNCTIONS  --------------------------------------------*)


EXTENDS Integers , Naturals, Sequences, FiniteSets, TLC   


CONSTANTS (*Sets containing the names of all the actors, mailboxes and mutexes *)
          Actors, MailboxesIds, MutexesIds,
          (*Set of all existing Memory addresses. Each actor has its own private Memory, indexed by these addresses *)
          Addresses

Actions == {\* All local actions are abstracted as a unique type
            "LocalComp",
       \* Communication actions
            "AsyncSend", "AsyncReceive", "TestAny", "WaitAny",
       \* Syncronization actions
        "AsyncMutexLock", "MutexUnlock", "MutexTestAny", "MutexWaitAny"
       }
NoActor == "NoActor"
NoAddress == "NoAddress"
          
VARIABLES doneCommunications, Memory, Mutex, Locks, Mailboxes, AsyncCount

(* Initially there are no doneCommunications, no Locks on the mutexes, Memory has random values *)

Init == /\ doneCommunications = { }
        (*Set Memory for running model*)
        /\ Memory \in [Actors -> [Addresses -> 0..Cardinality(Addresses)]]
        /\ Mutex = [i \in MutexesIds |-> <<>>] 
        /\ Mailboxes = [i \in MailboxesIds |-> <<>>] 
        /\ Locks = [i \in Actors |-> {}]
        /\ AsyncCount = 0



(* Comm type is declared as a structure *)  
Comm == [status:{"send", "receive", "done"},
         src:  Actors \cup { NoActor },
         dst:  Actors  \cup { NoActor },
         data_src:   Addresses \cup { NoAddress },
         data_dst:  Addresses \cup { NoAddress }]

(* Invariants to check that everything is in the right domains *)
TypeOK == /\ \forall c \in doneCommunications : c \in Comm /\ c.status = "done" 

          /\ \forall mbId \in MailboxesIds: ~\exists c \in DOMAIN Mailboxes[mbId]:
                         \/ Mailboxes[mbId][c] \notin Comm
                         \/ Mailboxes[mbId][c].status \notin {"send", "receive"}  
                         \/ \exists c1 \in DOMAIN Mailboxes[mbId] : Mailboxes[mbId][c].status /= Mailboxes[mbId][c1].status
                                                     
          /\ \forall mId \in MutexesIds: \forall id \in  DOMAIN Mutex[mId]: Mutex[mId][id] \in Actors

      /\ \forall act  \in Actors:  act /= NoActor
      /\ \forall addr \in Addresses: addr /= NoAddress

Constraint == /\ Cardinality(doneCommunications) \leq 3
              /\ \forall mbId \in MailboxesIds: Len(Mailboxes[mbId]) \leq 3
              /\ \forall mId \in MutexesIds: Len(Mutex[mId]) \leq 3
              /\ AsyncCount \leq 3

Symmetry == Permutations(Actors) \cup Permutations(MutexesIds) \cup Permutations(MailboxesIds)

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

convertToSet(S) =={S[i]: i  \in DOMAIN S  }

getNotDoneComms(S) ==  UNION { convertToSet(S[i]): i  \in DOMAIN S }

   
(* ---------------------------------------------------- LOCAL SUBSYSTEM ---------------------------------------------*)


(* A local computation of Actor <aId> can change the value of this Actor's Memory at any address *)

Local(aId) ==
    /\ aId \in Actors
    \*change value of Memory[aId][a], set {0,1,2,3,4,5} just for running model
    /\ Memory' \in [Actors -> [Addresses -> {0,1,2,3,4,5}]]
    /\ UNCHANGED <<doneCommunications, Mutex, Locks, Mailboxes, AsyncCount >>


(* ---------------------------------------------COMMUNICATION SUBSYSTEM -----------------------------------*)

(* AsyncSend(aId,mbId,data_addr):  
    the actor <aId> sends a "send" request to the mailbox <mbId>. 
    If a pending "receive" request already exists,
      they are combined to create a "done" paired communication in doneCommunications and data is copied from the source to the destination 
    otherwise a new communication with "send" status is created,
      address <data_addr> of Actor <aId> contains the data to transmit

  Parameters:
    - aId: the Actors of the sender 
    - mbId: the MailboxesIds where the "send" communication request is pushed 
    - data_addr: the address in the AsyncSender's Memory where the data to transmit is stored 
*)
 
AsyncSend(aId, mbId, data_addr) == 
  /\ aId \in Actors
  /\ mbId\in MailboxesIds
  /\ data_addr \in Addresses
        (*If the maibox is empty or contains only send doneCommunications, create a "send" communication in the mailbox *)
  /\ \/ /\ \/  Len(Mailboxes[mbId]) = 0
           \/ /\ Len(Mailboxes[mbId]) > 0 
              /\ Head(Mailboxes[mbId]).status = "send" 
        /\ LET comm ==  
                 [status |-> "send", 
                  src |-> aId,
                  dst |-> NoActor, 
                  data_src |-> data_addr,
                  data_dst |-> NoAddress]
            IN
                /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Append(Mailboxes[mbId],comm)]
        /\ AsyncCount' = AsyncCount + 1
                /\ UNCHANGED <<Memory, doneCommunications>>    
                
        (*Else the mailbox is not empty *)
     \/ /\ Len(Mailboxes[mbId]) >  0
        /\ Head(Mailboxes[mbId]).status = "receive"    
        /\ LET comm == Head(Mailboxes[mbId])
                (*If a matching "receive" request exists in the Mailboxes(mbId), choose the oldest one and
                    complete the Sender fields, set the communication to the "done" state and copy the data*)
           IN \/ /\ doneCommunications' = 
                    doneCommunications \cup {[comm EXCEPT
                                       !.status = "done",
                                       !.src = aId,
                                       !.data_src = data_addr]}
                 /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Tail(Mailboxes[mbId])]
                 /\ Memory' = [Memory EXCEPT ![comm.dst][comm.data_dst] = 
                                                    Memory[aId][data_addr]]
        /\ UNCHANGED <<AsyncCount>>                         
  /\ UNCHANGED << Mutex, Locks>> 

(* AsyncReceive(aId,mbId,data_addr): the actor <aId> sends a "receive" request to the mailbox <mbId>.
   If there is a pending "send" request on the same mailbox <mbId>, they are combined to create a "done" paired 
   communication in doneCommunications and data is coppied from the source to the destination, 
   otherwise a new communication is created with "receive" status.
   the address <data_addr> 
   
  Parameters: 
    - aId: the Actor ID of the receiver 
    - mbId: the mailbox where the "receive" communication request is going to be pushed 
    - data_addr: the address in the receivers's Memory where the data is going to be stored 
 *)
    
AsyncReceive(aId, mbId, data_addr) == 
  /\ aId \in Actors
  /\ mbId\in MailboxesIds
  /\ data_addr \in Addresses
    (*If the maibox is empty or contains only "receive" doneCommunications, create a "receive" communication in the mailbox *)
  /\ \/ /\ \/ Len(Mailboxes[mbId]) = 0
           \/ /\ Len(Mailboxes[mbId]) > 0 
              /\ Head(Mailboxes[mbId]).status = "receive"
        /\ LET comm ==  
                 [status |-> "receive", 
                  src |-> NoActor,
                  dst |-> aId, 
                  data_src |-> NoAddress,
                  data_dst |-> data_addr]
           IN
             /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Append(Mailboxes[mbId], comm)]
         /\ AsyncCount' = AsyncCount + 1
             /\ UNCHANGED <<Memory, doneCommunications>>    
            (*Else the mailbox is not empty *)
     \/ /\ Len(Mailboxes[mbId]) >  0
        /\ Head(Mailboxes[mbId]).status = "send"     
        /\ LET comm == Head(Mailboxes[mbId]) 
           (* If a matching "send" request exists in the mailbox mbId, choose the oldest one and,
            complete the receiver's fields and set the communication to the "done" state *)
           IN \/ /\ doneCommunications' = 
                    doneCommunications \cup {[comm EXCEPT
                                       !.status = "done",
                                       !.dst = aId,
                                       !.data_dst = data_addr
                                        ]}
                 /\ Memory' = [Memory EXCEPT ![aId][data_addr] = 
                                                    Memory[comm.src][comm.data_src]]
                 /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Tail(Mailboxes[mbId])]
         /\ UNCHANGED <<AsyncCount>>
  /\ UNCHANGED <<Mutex, Locks>> 

(* Wait(aId,comms):  Actor <aId> waits for at least one communication from a given set <comms> to complete 
    If it is already "done", there is nothing to do.
    Else the function is blocking when no communication is "done".   
 Parameters:
    - aId: the Actor's ID issuing the wait request
    - comms: list of doneCommunications on which the Actor is waiting
*)

WaitAny(aId, comms) ==
  /\ aId \in Actors
  /\ \E comm \in comms: comm \in doneCommunications
  /\ UNCHANGED <<Mutex, Locks, Mailboxes, Memory, doneCommunications, AsyncCount >>
 (* otherwise i.e. no communication in <comms> is  "done", WaitAny is blocking *)


(* Test(aId, comms, testResult_Addr): Actor <aId> waits for at least one communication from a given list <comms> to complete,
    and returns the boolean result at Memory adress <testResult_Addr>.
    The function is very similar to Wait, but returns a boolean value as a result, and is never blocking.
    Parameters
    - aId: the Actor ID issuing the test request 
    - comms: the list of doneCommunications on which we test
    - testResult_Addr: the address in the Actor Memory where the boolean result is going to be stored
*)
    

TestAny(aId, comms, testResult_Addr) ==
\*  /\ aId \in Actors
\*  /\ testResult_Addr \in Addresses
  (* If one of the doneCommunications is "done" return TRUE; else return FALSE *)
  /\ \/ /\ \E comm \in comms: comm \in doneCommunications
        /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = 1] (*True*)
     \/ /\ ~ \E comm \in comms: comm \in doneCommunications
        /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = 0] (*False*)
  /\ UNCHANGED <<doneCommunications, Mutex, Locks, Mailboxes, AsyncCount>>
  

(* -------------------------------- SYNCHRONIZATION SUBSYSTEM ----------------------------------------------------*)
                                
(* MutexAsyncLock(aId, mid, req_a) : Actor <aId> is requesting a lock on mutex <mid>. If allowed, address <req_a> stores the mutex id <mid>.    
- If the actor <aId> has no pending request on mutex <mid>, a new one is created 
        - add pair [mid,req_a] in Request[aId]
        - store <mid> in Memory[aId][req_a], i.e. local address <req_a> is assigned value <mid>
        - enqueue <aId> in Mutex[mid]
 The operation is non-blocking
*) 
 
 
 MutexAsyncLock(aId, mId, req_addr) ==
   /\ aId \in Actors
   /\ mId \in MutexesIds
   /\ req_addr \in Addresses
         (* if Actor <aId> has no pending request on mutex <mid>, create a new one *)      
   /\ \/ /\ ~isMember(aId, Mutex[mId])
         /\  Locks'  = [Locks EXCEPT ![aId]= Locks[aId] \cup {mId}]
         /\  Memory' = [Memory EXCEPT ![aId][req_addr] = mId]  
         /\  Mutex' = [Mutex EXCEPT ![mId] = Append(Mutex[mId], aId)]
         (* otherwise i.e. actor <aId> alreadly has a pending request on mutex <mid>, keep the variables unchanged *)          
      \/ /\ isMember(aId, Mutex[mId]) 
         /\ UNCHANGED <<Mutex,  Memory, Locks>>
   /\ AsyncCount' = AsyncCount+1        
   /\ UNCHANGED <<doneCommunications, Mailboxes>>
  
(* MutexUnlock(aId, mId): the Actor <aId> wants to release the mutex <mid>
    - it is either a normal unlock when <aId> owns <mid> (it is head of Mutex[mid]) 
    - or a cancel otherwise. 
    In both cases all links between <mid> and <aId> are removed in Mutex[mid] and Locks[aId] 
 *)
 
MutexUnlock(aId, mId) ==
   /\ aId \in Actors
   /\ isHead(aId, Mutex[mId])
   /\ Mutex' = [Mutex EXCEPT ![mId] = remove(aId,Mutex[mId])]
   /\ Locks' = [Locks EXCEPT ![aId] = Locks[aId] \ {mId} ]
   /\ UNCHANGED <<Memory, doneCommunications, Mailboxes, AsyncCount>>
   
   (* Otherwise, the transition is not enabled and Actor <aId> is blocked *)
   
   
(* MutexWaitAny(aId, req_addr): Actor <aId> waits for a lock request whose id is store in <req_addr>, 
  - if there is a req in Locks[aId] whose mid is store in  <req_addr>, and <aId> is the owner of this mutex mid (head of Mutex[req.id]), 
    then MutexWaitAny is enabled
  - otherwise the transition is not enabled.
  MutexWaitAny is thus blocking until <aId> owns the mutex 
 *)

MutexWaitAny(aId, locks) == 
/\ aId \in Actors
(* If req_a is the id of a Request of Actor <aId>, and <aId> is the owner of this mutex, <aId> proceeds*) 
/\ \E req \in  locks : isHead(aId, Mutex[req])
/\ UNCHANGED << Memory, Mutex, Locks, doneCommunications, Mailboxes, AsyncCount>>

(* otherwise <aId> is blocked *)  


(* MutexTestAny(aId,req_addr, result_addr): actor <aId> tests if he is the owner of the mutex whose id is store in <req_addr>
            (i.e. he is the head of the mutex Mutex)
            and stores the boolean result at address <testResult_Addr> 
            MutexTestAny is non-blocking
            *)
            
            
            
MutexTestAny(aId, locks, testResult_Addr) ==
  /\ aId \in Actors
  /\ testResult_Addr \in Addresses
  /\  \/ /\ \E req \in  locks: isHead(aId, Mutex[req]) 
         /\ /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = 1 (*TRUE*)]
      \/ /\ ~\E req \in  locks: isHead(aId, Mutex[req]) 
         /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = 0 (*FALSE*)] 
  /\ UNCHANGED <<Mutex, Locks, doneCommunications, Mailboxes, AsyncCount>>


--------------------------------------------------------------------------------------------------------------------------------
                                    (*INDICATE NEXT ACTIONS *)
                                    
(* Next indicates the possible actions that could be fired at a state  *)
Next ==   \/ \E actor \in Actors, mb \in MailboxesIds, addr \in Addresses:
             AsyncSend(actor, mb, addr)
          \/ \E actor \in Actors, mb \in MailboxesIds, addr \in Addresses:
             AsyncReceive(actor, mb, addr)
          (*\/ \E actor \in Actors, \E comms \in SUBSET  doneCommunications :*)
          \/ \E actor \in Actors: \E comms \in SUBSET  ( doneCommunications \cup getNotDoneComms(Mailboxes) ):
                WaitAny(actor, comms)
          \/ \E actor \in Actors : \E comms \in SUBSET ( doneCommunications \cup getNotDoneComms(Mailboxes) ) , addr \in Addresses:
                TestAny(actor, comms, addr)
          \/ \E actor \in Actors:   Local(actor) 
          
          \/ \E actor \in Actors, mutex \in MutexesIds, addr \in Addresses:
            MutexAsyncLock(actor, mutex, addr)
            
            
          \/ \E actor \in Actors: \E   locks \in SUBSET Locks[actor]:
            MutexWaitAny(actor, locks)
            
          \/ \E actor \in Actors: \E  locks \in SUBSET Locks[actor], addr \in Addresses:
          
            MutexTestAny(actor, locks , addr) 
          \/ \E actor \in Actors, mutex \in MutexesIds:
          
             MutexUnlock(actor, mutex) 
-----------------------------------------------------------------------------------------------------------------

(* Definition of the Independence relation *)

           (*Executing A does not enable or disable B*) 
I(A,B) == /\ ENABLED A =>   /\ ENABLED B => (A => (ENABLED B)')
                            /\ (A => (ENABLED B)') =>  ENABLED B 
           (*if both A and B are enabled, their execution can be commuted*)
          /\ (ENABLED  A /\ ENABLED B)  => ( A \cdot B \equiv B \cdot A )

-----------------------------------------------------------------------------------------------------------------
(* ------------------------------------------ INDEPENDENCE THEOREMS-----------------------------------------------------*)

(* Independence theorems for doneCommunications *)

(* AsyncSend and AsyncReceive are always independent *)


THEOREM \forall a1, a2 \in Actors, mbId1, mbId2 \in MailboxesIds, data1, data2 \in Addresses:
           a1 /= a2 => 
           I(AsyncSend(a1, mbId1, data1), AsyncReceive(a2, mbId2, data2))

\* WROOOONG
THEOREM \forall a1, a2 \in Actors, mb \in MailboxesIds, data1, data2 \in Addresses:
               a1 # a2  => I(AsyncSend(a1, mb, data1), AsyncSend(a2, mb, data2))
           
\* WROOOONG
THEOREM \forall a1, a2 \in Actors, mb1, mb2 \in MailboxesIds: a1 # a2 => mb1 # mb2
           

(* two AsyncSend  or two AsyncReceive are independent if they concern different mailboxes *)
THEOREM \forall a1, a2 \in Actors, mbId1, mbId2 \in MailboxesIds, data1, data2 \in Addresses:
        /\ a1 /= a2 
        /\ mbId1 /= mbId2
        (* /\ ENABLED AsyncReceive(a1, mbId1, data1)
           /\ ENABLED AsyncReceive(a2, mbId2, data2) 
           *)
         => /\ I(AsyncSend(a1, mbId1, data1), AsyncSend(a2, mbId2, data2)) 
            /\ I(AsyncReceive(a1, mbId1, data1),  AsyncReceive(a2, mbId2, data2))




(* two WaitAny actions, or two TestAny actions, or a WaitAny action and a TestAny are independent*)
THEOREM \forall a1, a2 \in Actors, comms1, comms2 \in SUBSET doneCommunications, test_r1, test_r2 \in Addresses:
        a1 /= a2 => 
           /\ I(WaitAny(a1, comms1), WaitAny(a2, comms2))
           /\ I(TestAny(a1, comms1, test_r1), TestAny(a2, comms2, test_r2))   
           /\ I(WaitAny(a1, comms1), TestAny(a2, comms2, test_r2))
  

(* A WaitAny action or a TestAny action and a AsyncSend action or a 
AsyncReceive action are independent if they concern different communication. *)
(* !!! Unsure about conditions for independence *)
(*
THEOREM \forall a1, a2 \in Actors, data, comm1, comm2, test_r \in Addresses, mbId\in MailboxesIds:
              /\ a1 /= a2
              /\ Memory[a1][comm1] /=   Memory[a1][comm2]
                 =>  /\ I( WaitAny(a1, {comm1}), AsyncSend(a2, mbId, data, comm2)) 
                     /\ I( WaitAny(a1, {comm1}), AsyncReceive(a2, mbId, data, comm2)) 
                     /\ I(TestAny(a1, {comm1}, test_r ), AsyncSend(a2, mbId, data, comm2))
                     /\ I( TestAny(a1, {comm1}, test_r ), AsyncReceive(a2, mbId, data, comm2))  
*)

(*Two synchronization actions (\mutexlock, \mutexunlock) 
are independent if they concern different mutexes and performed by different actors.*)
THEOREM \forall a1, a2 \in Actors, mt1, mt2 \in MutexesIds, req1, req2, test_r \in Addresses:
        /\ a1 /= a2
        /\ mt1 /= mt2
        /\ Memory[a2][req1] /= mt1
        => /\ I(MutexAsyncLock(a1, mt1, req1), MutexAsyncLock(a2, mt2, req2))
           /\ I(MutexAsyncLock(a1, mt1, req1), MutexUnlock(a2, mt2))
           /\ I(MutexUnlock(a1, mt2), MutexUnlock(a2, mt2))
           /\ I(MutexAsyncLock(a1, mt1, req1), MutexTestAny(a2, req2, test_r))      
           /\ I(MutexAsyncLock(a1, mt1, req1), MutexWaitAny(a2, req1))      
           /\ I(MutexUnlock(a1, mt1), MutexUnlock(a2, mt2))
           /\ I(MutexUnlock(a1, mt1), MutexWaitAny(a2, req1))
           /\ I(MutexUnlock(a1, mt1), MutexTestAny(a2, req1, test_r))

(* MutexAsyncLock actions and MutexUnlock action are independent*)
 
THEOREM \forall a1, a2 \in Actors, mt1, mt2 \in MutexesIds, req1, req2 \in Addresses:
        /\ a1 /= a2 =>  I(MutexAsyncLock(a1, mt1, req1), MutexUnlock(a2, req2))

      
 (*Two MutexWaitAny actions, two MutexTestAny actions, a MutexWaitAny action and MutexTestAny action are independent*)             
THEOREM \forall a1, a2 \in Actors, mt1, mt2 \in MutexesIds, req1, req2, test_r1, test_r2 \in Addresses,  
           comm_addrs1 , comm_addrs2 \in SUBSET Addresses:
           a1 /= a2 => 
           /\ I(MutexWaitAny(a1, req1), MutexWaitAny(a2, req2))
           /\ I(MutexWaitAny(a1, req1), MutexTestAny(a2, req1, test_r1))
           /\ I(MutexTestAny(a1, req1, test_r1), MutexTestAny(a2, req2, test_r2))
           
 (* A MutexAsyncLock action and a MutexWaitAny action or MutexTestAny action are independent*)
 THEOREM \forall a1, a2 \in Actors, mt \in MutexesIds, req1, req2, test_r \in Addresses:
         a1 /= a2 =>
         /\ I(MutexAsyncLock(a1, mt, req1), MutexWaitAny(a2, req2))
         /\ I(MutexAsyncLock(a1, mt, req1), MutexTestAny(a1, req2, test_r))

 (* A MutexUnlock action and a MutexWaitAny action or MutexTestAny action are independent if concern different mutexes*)
THEOREM \forall a1, a2 \in Actors, mt \in MutexesIds, test_r, req, req1 \in Addresses:
            /\ a1 /= a2 
            /\ Memory[a1][req] /= mt => /\ I(MutexUnlock(a1, req1), MutexWaitAny(a2, req))
                                        /\ I(MutexUnlock(a1, req1), MutexTestAny(a2, req, test_r))


 (*A synchoronization action (MutexAsyncLock, MutexUnlock, MutexWaitAny, MutexTestAny) is independent with 
 a communication action (AsyncSend, AsyncReceive, TestAny, WaitAny) if they are performed by different actors*)
 
THEOREM \forall a1, a2 \in Actors, mt \in MutexesIds, req,  data, comm, test_r1,  test_r2 \in Addresses,
         mbId\in MailboxesIds, comm_addrs \in SUBSET Addresses:
           a1 /= a2 =>
           /\ I(MutexAsyncLock(a1, mt, req), AsyncSend(a2, mbId, data))
           /\ I(MutexAsyncLock(a1, mt, req), AsyncReceive(a2, mbId, data))  
           /\ I(MutexAsyncLock(a1, mt, req), WaitAny(a2, comm_addrs))   
           /\ I(MutexAsyncLock(a1, mt, req), TestAny(a2, comm_addrs, test_r1))   
           
           /\ I(MutexUnlock(a1, mt), AsyncSend(a2, mbId, data))
           /\ I(MutexUnlock(a1, mt), AsyncReceive(a2, mbId, data))  
           /\ I(MutexUnlock(a1, mt), WaitAny(a2, comm_addrs))   
           /\ I(MutexUnlock(a1, mt), TestAny(a2, comm_addrs, test_r1))
              
           /\ I(MutexWaitAny(a1, req), AsyncSend(a2, mbId, data))
           /\ I(MutexWaitAny(a1, req), AsyncReceive(a2, mbId, data))
           /\ I(MutexWaitAny(a1, req), WaitAny(a2, comm_addrs))
           /\ I(MutexWaitAny(a1, req), TestAny(a2, comm_addrs, test_r1))
          
           /\ I(MutexTestAny(a1, req, test_r1), AsyncSend(a2, mbId, data))
           /\ I(MutexTestAny(a1, req, test_r1), AsyncReceive(a2, mbId, data))
           /\ I(MutexTestAny(a1, req, test_r1), WaitAny(a2, comm_addrs))   
           /\ I(MutexTestAny(a1, req, test_r1), TestAny(a2, comm_addrs, test_r2))   
           
 (*A LocalComputation action is independent with all other actions*)
 THEOREM \forall a1, a2 \in Actors, mt \in MutexesIds, req,  data, comm, test_r \in Addresses,
         mbId\in MailboxesIds, comm_addrs \in SUBSET Addresses:
           a1 /= a2 =>
           /\ I(Local(a1), AsyncSend(a2, mbId, data))
           /\ I(Local(a1), AsyncReceive(a2, mbId, data))  
           /\ I(Local(a1), WaitAny(a2, comm_addrs))   
           /\ I(Local(a1), TestAny(a2, comm_addrs, test_r))   
           /\ I(Local(a1), MutexWaitAny(a2, req))
           /\ I(Local(a1), MutexTestAny(a2, req, test_r))
           /\ I(Local(a1), MutexUnlock(a2, mt))
           /\ I(Local(a1), MutexUnlock(a2, mt))
 
-------------------------------------------------
Spec == /\ Init
        /\ [][Next]_<< doneCommunications, Memory, Mutex, Locks, Mailboxes, AsyncCount >>

=============================================================================
