--------------------------- MODULE abstractModel2 ---------------------------
(*THERE ARE COMMUNICATION IDS IN THIS VERSION FOR EXPRESSING INDEPENDENE THEOREMS*)


(*This specification formally describes (builds the formal model of) programs/distributed systems that are simulated in SimGrid. 
    It focuses on modeling the how the global state of the system evoluates by the effect of actions: 
                   
                   current state
                        |
                        |
                        | action
                        |
                        v
                   next state 
                   
  - The state of the system is represented by 6 variables: Communications, Mailboxes, Memory, Mutexes, nbComMbs and Requests
    + Communications is the set of all paired communications in the system (i.e. when a pair of send and receive requests have been matched) 
    + Mailboxes is an array indexed by MailboxesIds ; Mailboxes[mId] is a FIFO queue which stores send or receive requests (unpaired communications),
    + Memory is an array indexed by Actors, Memory[aId] is a memory LocalComp to the actor aId used to store ids of communications, ids of Requests and values of LocalComp variables 
    + pc is an array indexed by Actors; pc[aId] represents the program counter of the actor aId, changed  after firing each action 
    + Mutexes is an array indexed by MutexIds; Mutexes[mId] is a FIFO queue that remembers which actors have required the Mutexes 
    + Requests is an array indexed by Actors; Requests[aId] is the set of all the MutexIds requested by the actor aId   
    + commId is used to set id for communications
  - Actions are structured in 3 subsystems:
    - the LocalComp actions :  LocalComp, 
    - the Communication actions: AsyncSend, AsyncReceive, Wait, Test,
    - the Synchronization actions: MutexesAsyncLock, MutexUnlock, MutexTestAny and MutexWaitAny.
   *)
   
(*---------------------------- GENERAL CONSTANTS, VARIABLES, FUNCTIONS  --------------------------------------------*)


EXTENDS Integers , Naturals, Sequences, FiniteSets, TLC   


CONSTANTS (*Sets containing the names of all the actors, mailboxes and Mutexes *)
          Actors, MailboxesIds, MutexIds,
          (*Set of all existing Memory addresses. Each actor has its own private Memory, indexed by these addresses *)
          Addresses
          
VARIABLES Communications, Memory,  Mutexes, Requests, Mailboxes,  nbComMbs, nbtest

NoActor == "NoActor"
NoAddr == "NoAddress"
     


(* Initially there are no Communications, no Requests on the Mutexes, Memory has random values *)

Init == /\ Communications = { }
        /\ Memory \in [Actors -> [Addresses -> {"zero"}   ] ]
        \*/\ Memory = [i \in Actors, j \in Addresses |-> "zero" ]
        /\ Mutexes = [i \in MutexIds |-> <<>>] 
        /\ Mailboxes = [i \in MailboxesIds |-> <<>>] 
        /\ Requests = [i \in Actors |-> {}]
        (*/\ pc = CHOOSE f \in [Actors -> Instr] : TRUE*)
        /\ nbComMbs =  [i \in MailboxesIds |-> 0]        
        /\ nbtest = 0
        
        
(* Comm type is declared as a structure *)  
Comm == [id: STRING,
         status:{"send", "receive", "done"},
         src:  Actors \cup { NoActor },
         dst:  Actors  \cup { NoActor },
         data_src:   Addresses \cup { NoAddr },
         data_dst:  Addresses \cup { NoAddr }]

(* Invariants to check everything in the right domains*)
TypeInv == /\ \forall c \in Communications : c \in Comm /\ c.status = "done" 

           /\ \forall mbId \in MailboxesIds: ~\exists c \in DOMAIN Mailboxes[mbId]:
                         \/ Mailboxes[mbId][c] \notin Comm
                         \/ Mailboxes[mbId][c].status \notin {"send", "receive"}  
                         \/ \exists c1 \in DOMAIN Mailboxes[mbId] : Mailboxes[mbId][c].status /= Mailboxes[mbId][c1].status
                                                     
           /\ \forall mId \in MutexIds: \forall id \in  DOMAIN Mutexes[mId]: Mutexes[mId][id] \in Actors


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

converToString(x,y,z) == ToString(x) \circ y \circ ToString(z)  

(*This function should return id of first done communication in Comms, here is only PROTOTYPE, used only for expressing theorems   *)
firstDone(Comms) == 1
  
 twoFirstOwner (mt,a1,a2) == IF ( ~ (getIndex(a1,Mutexes[mt]) \in { 1,2}) \/  ~ (getIndex(a2,Mutexes[mt]) \in { 1,2})) THEN FALSE
                             ELSE TRUE
  
(* ---------------------------------------------------- LocalComp SUBSYSTEM ---------------------------------------------*)


(* A LocalComp computaion of Actor <aId> can change the value of this Actor's Memory at any address *)

LocalComp(aId) ==
    /\ aId \in Actors
    \*change value of Memory[aId][a], set {0,1,2,3,4,5} just for running model
    /\ Memory' \in [Actors -> [Addresses -> {"a", "b", "c"}  ] ]
    /\ UNCHANGED <<Communications, Mutexes, Requests, Mailboxes, nbComMbs, nbtest >>


(* ---------------------------------------------COMMUNICATION SUBSYSTEM -----------------------------------*)

(* AsyncSend(aId,mbId,data_addr,comm_addr):  
    the actor <aId> sends a "send" request to the mailbox <mbId>. 
    If a pending "receive" request already exists, they are combined to create a "done" paired communication in Communications and
    data is copied from the source to the destination 
    otherwise a new communication with "send" status is created,
    address <data_addr> of Actor <aId> contains the data to transmit,
    and Memory address <comm_addr> of Actor <aId> is assigned the id of the communication 

  Parameters:
    - aId: the Actors of the sender 
    - mbId: the MailboxesIds where the "send" communication request is pushed 
    - data_addr: the address in the AsyncSender's Memory where the data to transmit is stored 
    - comm_addr: the address in the AsyncSender's Memory where to store the communication id *)
 
AsyncSend(aId, mbId, data_addr, comm_addr) == 
  /\ aId \in Actors 
  /\ mbId\in MailboxesIds
  /\ data_addr \in Addresses
  /\ comm_addr \in Addresses
        (*If the maibox is empty or contains only send communications, create a "send" 
                                                             communication in the mailbox *)
  /\ \/ /\ \/  Len(Mailboxes[mbId]) = 0
           \/ /\ Len(Mailboxes[mbId]) > 0 
              /\ Head(Mailboxes[mbId]).status = "send" 
        /\ LET comm ==  
                 [id |->  converToString(nbComMbs[mbId], "Mb", mbId ),
                  status |-> "send", 
                  src |-> aId,
                  dst |-> NoActor, 
                  data_src |-> data_addr,
                  data_dst |-> NoAddr]
            IN
                /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Append(Mailboxes[mbId],comm)]
                /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id] 
                /\ UNCHANGED <<Communications>>    
                /\ nbComMbs' = [nbComMbs EXCEPT ![mbId] = nbComMbs[mbId]+1]                
        (*Else the mailbox is not empty *)
     \/ /\ Len(Mailboxes[mbId]) >  0
        /\ Head(Mailboxes[mbId]).status = "receive"    
        /\ LET comm == Head(Mailboxes[mbId])
                (*If a matching "receive" request exists in the Mailboxes(mbId), choose the oldest one and
                    complete the Sender fields, set the communication to the "done" state and copy the data*)
           IN    /\ Communications' = 
                    Communications \cup {[comm EXCEPT
                                       !.status = "done",
                                       !.src = aId,
                                       !.data_src = data_addr]}
                 /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Tail(Mailboxes[mbId])]
                 /\ Memory' = [Memory EXCEPT ![comm.dst][comm.data_dst] = 
                                                    Memory[aId][data_addr]]
                 /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id] 
                 /\ UNCHANGED <<nbComMbs, nbtest>>
  /\ UNCHANGED << Mutexes, Requests , nbtest>> 


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
  /\ aId \in Actors 
  /\ mbId\in MailboxesIds
  /\ data_addr \in Addresses
  /\ comm_addr \in Addresses
    (*If the maibox is empty or contains only "receive" communications, create a "receive" 
                                                                    communication in the mailbox *)
  /\ \/ /\ \/ Len(Mailboxes[mbId]) = 0
           \/ /\ Len(Mailboxes[mbId]) > 0 
              /\ Head(Mailboxes[mbId]).status = "receive"
        /\ LET comm ==  
                 [id |-> converToString(nbComMbs[mbId], "Mb", mbId ),
                  status |-> "receive", 
                  src |-> NoActor,
                  dst |-> aId, 
                  data_src |-> NoAddr,
                  data_dst |-> data_addr]
           IN
             /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Append(Mailboxes[mbId], comm)]
             /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id]
             /\ UNCHANGED <<Communications>>    
             /\ nbComMbs' = [nbComMbs EXCEPT ![aId] = nbComMbs[aId] +1 ]
            (*Else the mailbox is not empty *)
     \/ /\ Len(Mailboxes[mbId]) >  0
        /\ Head(Mailboxes[mbId]).status = "send"     
        /\ LET comm == Head(Mailboxes[mbId]) 
           (* If a matching "send" request exists in the mailbox mbId, choose the oldest one and,
            complete the receiver's fields and set the communication to the "done" state *)
           IN   /\ Communications' = 
                    Communications \cup {[comm EXCEPT
                                       !.status = "done",
                                       !.dst = aId,
                                       !.data_dst = data_addr
                                        ]}
                 /\ Memory' = [Memory EXCEPT ![aId][data_addr] = 
                                                    Memory[comm.src][comm.data_src]]
                 /\ Mailboxes' = [Mailboxes EXCEPT ![mbId] = Tail(Mailboxes[mbId])]
                 /\ Memory' = [Memory EXCEPT ![aId][comm_addr] = comm.id]
                 /\ UNCHANGED <<nbComMbs>>
  /\ UNCHANGED <<Mutexes, Requests , nbtest>> 

(* Wait(aId,comm_addrs):  Actor <aId> waits for at least one communication from a given set <comm_addrs> to complete 
    If it is already "done", there is nothing to do.
    Else the function is blocking when no communication is "done".   
 Parameters:
    - aId: the Actor's ID issuing the wait request
    - comm_addrs: the list of addresses in the Actor's Memory where the communication ids are stored 
*)

WaitAny(aId, comm_addrs) ==
  /\ aId \in Actors
  /\ \E comm_addr \in comm_addrs, comm \in Communications: comm.id = Memory[aId][comm_addr]
  /\ UNCHANGED <<Mutexes, Requests, Mailboxes, nbComMbs, Memory, Communications, nbtest >>
 (* otherwise i.e. no communication in <comm_addrs> is  "done", WaitAny is blocking *)


(* Test(aId, comm_addrs, testResult_Addr): Actor <aId> waits for at least one communication from a given list <comm_addrs> to complete,
    and returns the boolean result at Memory adress <testResult_Addr>.
    The function is very similar to Wait, but returns a boolean value as a result, and is never blocking.
    Parameters
    - aId: the Actor ID issuing the test request 
    - comm_addrs: the list of addresses in the Actor's Memory where the communication ids are stored 
    - testResult_Addr: the address in the Actor Memory where the boolean result is going to be stored *)
    

TestAny(aId, comm_addrs, testResult_Addr) ==
  /\ aId \in Actors
  /\ testResult_Addr \in Addresses
  /\ \/ /\ \E comm_addr \in comm_addrs, comm \in Communications: comm.id = Memory[aId][comm_addr]
        (* If the communication is "done" return ValTrue *)
        /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = "true"]
          \* /\ nbtest' =  nbtest +1
        (* if no communication is "done", return ValFalse *)   
     \/ /\ ~ \exists comm_addr \in comm_addrs, comm \in Communications: comm.id = Memory[aId][comm_addr]
        /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = "false"]
        /\ UNCHANGED  nbtest
  (* Test is non-blocking since in all cases pc[aId] is incremented *)
  /\ UNCHANGED <<Mutexes, Requests, Mailboxes,Communications, nbComMbs, nbtest>>
  
(* -------------------------------- SYNCHRONIZATION SUBSYSTEM ----------------------------------------------------*)
                                
(* MutexesAsyncLock(aId, mid, req_a) : Actor <aId> is requesting a lock on Mutexes <mid>. If allowed, address <req_a> stores the Mutexes id <mid>.    
- If the actor <aId> has no pending request on Mutexes <mid>, a new one is created 
        - add pair [mid,req_a] in Request[aId]
        - store <mid> in Memory[aId][req_a], i.e. LocalComp address <req_a> is assigned value <mid>
        - enqueue <aId> in Mutexes[mid]
 The operation is non-blocking
*) 
 
 
 AsyncMutexLock(aId, mId) ==
   /\ aId \in Actors
   /\ mId \in MutexIds
         (* if Actor <aId> has no pending request on Mutexes <mid>, create a new one *)      
   /\ \/ /\ ~isMember(aId, Mutexes[mId])
         /\  Requests'  = [Requests EXCEPT ![aId]= Requests[aId] \cup {mId}]
         /\  Mutexes' = [Mutexes EXCEPT ![mId] = Append(Mutexes[mId], aId)]
         (* otherwise i.e. actor <aId> alreadly has a pending request on Mutexes <mid>, keep the variables unchanged *)          
      \/ /\ isMember(aId, Mutexes[mId]) 
         /\ UNCHANGED <<Mutexes,  Requests>>
   /\ UNCHANGED <<Communications, Mailboxes, nbtest, nbComMbs ,  Memory>>
  
(* MutexUnlock(aId, mId): the Actor <aId> wants to release the Mutexes <mid>
    - it is either a normal unlock when <aId> owns <mid> (it is head of Mutexes[mid]) 
    - or a cancel otherwise. 
    In both cases all links between <mid> and <aId> are removed in Mutexes[mid] and Requests[aId] 
 *)
 
MutexUnlock(aId, mId) ==
   /\ aId \in Actors
   /\ \/ /\ isMember(aId, Mutexes[mId])
         /\ Mutexes' = [Mutexes EXCEPT ![mId] = remove(aId,Mutexes[mId])]
         /\ Requests' = [Requests EXCEPT ![aId] = Requests[aId] \ {mId} ]
         /\ UNCHANGED <<Memory, Communications, Mailboxes, nbtest, nbComMbs >>
      \/ /\ ~isMember(aId, Mutexes[mId])
         /\ UNCHANGED <<Memory, Communications, Mailboxes, nbtest, nbComMbs, Requests,Mutexes >>
   
   
   
(* MutexWaitAnyAny(aId, req_addr): Actor <aId> waits for a lock request whose id is store in <req_addr>, 
  - if there is a req in Requests[aId] whose mid is store in  <req_addr>, and <aId> is the owner of this Mutexes mid (head of Mutexes[req.id]), 
    then MutexWaitAnyAny is enabled
  - otherwise the transition is not enabled.
  MutexWaitAnyAny is thus blocking until <aId> owns the Mutexes 
 *)

MutexWaitAny(aId, requests) == 
/\ aId \in Actors
(* If req_a is the id of a Request of Actor <aId>, and <aId> is the owner of this Mutexes, <aId> proceeds*) 
/\ \E req \in  requests : isHead(aId, Mutexes[req])
/\ UNCHANGED << Memory, Mutexes, Requests, Communications, Mailboxes, nbtest, nbComMbs >>

(* otherwise <aId> is blocked *)  


(* MutexTestAnyAny(aId,req_addr, result_addr): actor <aId> tests if he is the owner of the Mutexes whose id is store in <req_addr>
            (i.e. he is the head of the Mutexes Mutexes)
            and stores the boolean result at address <testResult_Addr> 
            MutexTestAnyAny is non-blocking
            *)
            
            
            
MutexTestAny(aId, requests, testResult_Addr) ==
  /\ aId \in Actors
  /\ testResult_Addr \in Addresses
  /\  \/ /\ \E req \in  requests: isHead(aId, Mutexes[req]) 
         /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = "true" (*TRUE*)]
      \/ /\ ~\E req \in  requests: isHead(aId, Mutexes[req]) 
         /\ Memory' = [Memory EXCEPT ![aId][testResult_Addr] = "false" (*FALSE*)] 
         /\ UNCHANGED nbtest 
  /\ UNCHANGED <<Mutexes, Requests, Communications, Mailboxes, nbComMbs, nbtest >>

--------------------------------------------------------------------------------------------------------------------------------
                                    (*INDICATE NEXT ACTIONS *)
                                    
(* Next indicates the possible actions that could be fired at a state  *)
Next ==   \/  \E actor \in Actors, mbId \in MailboxesIds, data_addr, comm_addr \in  Addresses:      
               AsyncSend(actor, mbId, data_addr, comm_addr)
          \/  \E actor \in Actors, mbId\in MailboxesIds, data_addr, comm_addr \in  Addresses:      
               AsyncReceive(actor, mbId, data_addr, comm_addr)
          \/  \E actor \in Actors, comm_addrs \in SUBSET Addresses:      
               WaitAny(actor, comm_addrs)
          \/  \E actor \in Actors,  result_addr \in  Addresses, comm_addrs  \in SUBSET Addresses :      
               TestAny(actor, comm_addrs, result_addr)
          \/  \E actor \in Actors:
               LocalComp(actor)
          \/ \E actor \in Actors, mt \in MutexIds, addr \in Addresses:
              AsyncMutexLock(actor, mt)
          \/ \E actor \in Actors: \E   requests \in SUBSET Requests[actor]:
              MutexWaitAny(actor, requests)
          \/ \E actor \in Actors: \E  requests \in SUBSET Requests[actor], addr \in Addresses:
              MutexTestAny(actor, requests , addr) 
          \/ \E actor \in Actors, mt \in MutexIds:
             MutexUnlock(actor, mt)  

Spec == Init /\ [][Next]_<< Communications, Memory, Mutexes, Requests, Mailboxes, nbComMbs, nbtest >>
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

 (*A LocalCompComputation action is independent with all other actions*)
 THEOREM \forall a1, a2 \in Actors, mt \in MutexIds,   data, comm, test_r \in Addresses,
         mbId\in MailboxesIds, comm_addrs \in SUBSET Addresses, reqs \in SUBSET MailboxesIds:
           a1 /= a2 =>
           /\ I(LocalComp(a1), AsyncSend(a2, mbId, data, comm))
           /\ I(LocalComp(a1), AsyncReceive(a2, mbId, data, comm))  
           /\ I(LocalComp(a1), WaitAny(a2, comm_addrs))   
           /\ I(LocalComp(a1), TestAny(a2, comm_addrs, test_r))   
           /\ I(LocalComp(a1), MutexWaitAny(a2,reqs ))
           /\ I(LocalComp(a1), MutexTestAny(a2, reqs, test_r))
           /\ I(LocalComp(a1), AsyncMutexLock(a2, mt))
           /\ I(LocalComp(a1), MutexUnlock(a2, mt))
 
 (*A synchoronization action (AsyncMutexLock, MutexUnlock, MutexWaitAny, MutexTestAny) is independent with 
 a communication action (AsyncSend, AsyncReceive, TestAny, WaitAny) if they are performed by different actors*)
 
THEOREM \forall a1, a2 \in Actors, mt \in MutexIds,  data, comm, test_r1,  test_r2 \in Addresses,
         mbId \in MailboxesIds, comm_addrs \in SUBSET Addresses, reqs \in SUBSET MutexIds:
           a1 /= a2 =>
           /\ I(AsyncMutexLock(a1, mt), AsyncSend(a2, mbId, data, comm))
           /\ I(AsyncMutexLock(a1, mt), AsyncReceive(a2, mbId, data, comm))  
           /\ I(AsyncMutexLock(a1, mt), WaitAny(a2, comm_addrs))   
           /\ I(AsyncMutexLock(a1, mt), TestAny(a2, comm_addrs, test_r1))   
           
           /\ I(MutexUnlock(a1, mt), AsyncSend(a2, mbId, data, comm))
           /\ I(MutexUnlock(a1, mt), AsyncReceive(a2, mbId, data, comm))  
           /\ I(MutexUnlock(a1, mt), WaitAny(a2, comm_addrs))   
           /\ I(MutexUnlock(a1, mt), TestAny(a2, comm_addrs, test_r1))
              
           /\ I(MutexWaitAny(a1, reqs), AsyncSend(a2, mbId, data, comm))
           /\ I(MutexWaitAny(a1, reqs), AsyncReceive(a2, mbId, data, comm))
           /\ I(MutexWaitAny(a1, reqs), WaitAny(a2, comm_addrs))
           /\ I(MutexWaitAny(a1, reqs), TestAny(a2, comm_addrs, test_r1))
          
           /\ I(MutexTestAny(a1, reqs, test_r1), AsyncSend(a2, mbId, data, comm))
           /\ I(MutexTestAny(a1, reqs, test_r1), AsyncReceive(a2, mbId, data, comm))
           /\ I(MutexTestAny(a1, reqs, test_r1), WaitAny(a2, comm_addrs))   
           /\ I(MutexTestAny(a1, reqs, test_r1), TestAny(a2, comm_addrs, test_r2))   
           


(* two AsyncSend  or two AsyncReceive are independent if they concern different mailboxes 
THEOREM \forall a1, a2 \in Actors, mbId1, mbId2 \in MailboxesIds, data1, data2, comm1, comm2 \in Addresses:
        /\ a1 /= a2 
        /\ mbId1 /= mbId2
  
         => /\ I(AsyncSend(a1, mbId1, data1, comm1), AsyncSend(a2, mbId2, data2, comm2)) 
            /\ I(AsyncReceive(a1, mbId1, data1, comm1),  AsyncReceive(a2, mbId2, data2, comm2))
*)

(* two communication actions are independent if they concern different mailboxes
   *)
THEOREM \forall a1, a2 \in Actors, mbId1, mbId2 \in MailboxesIds, data1, data2, comm1, comm2 \in Addresses:
        /\ a1 /= a2 
        /\ mbId1 /= mbId2
          => /\ I(AsyncSend(a1, mbId1, data1, comm1), AsyncSend(a2, mbId2, data2, comm2)) 
            /\ I(AsyncReceive(a1, mbId1, data1, comm1),  AsyncReceive(a2, mbId2, data2, comm2))
            /\ I(AsyncSend(a1, mbId1, data1, comm1), AsyncReceive(a2, mbId2, data2, comm2)) 




(* AsyncSend and AsyncReceive are always independent *)

THEOREM \forall a1, a2 \in Actors, mbId1, mbId2 \in MailboxesIds, data1, data2, comm1, comm2 \in Addresses:
           a1 /= a2 => 
           I(AsyncSend(a1, mbId1, data1, comm1), AsyncReceive(a2, mbId2, data2, comm2))
       
(* two WaitAny actions, or two TestAny actions, or a WaitAny action and a TestAny are independent*)
THEOREM \forall a1, a2 \in Actors, comms1, comms2 \in SUBSET Addresses, test_r1, test_r2 \in Addresses:
        a1 /= a2 => 
           /\ I(WaitAny(a1, comms1), WaitAny(a2, comms2))
           /\ I(TestAny(a1, comms1, test_r1), TestAny(a2, comms2, test_r2))   
           /\ I(WaitAny(a1, comms1), TestAny(a2, comms2, test_r2))
  

(* A WaitAny action or a TestAny action and a AsyncSend action or a 
AsyncReceive action are independent if they concern different communication. *)
(* !!! Unsure about conditions for independence *)

THEOREM \forall a1, a2 \in Actors, data, comm_addr, test_r \in Addresses,  comms \in SUBSET Addresses, mbId\in MailboxesIds:
              /\ a1 /= a2
              /\ ~\E comm \in comms: /\ Memory[a1][comm] /=   Memory[a2][comm_addr] 
                                     /\ firstDone(comms) /=   Memory[a2][comm_addr] 
                 =>  /\ I( WaitAny(a1, {comms}), AsyncSend(a2, mbId, data, comm_addr)) 
                     /\ I( WaitAny(a1, {comms}), AsyncReceive(a2, mbId, data, comm_addr)) 
                     /\ I(TestAny(a1, {comms}, test_r ), AsyncSend(a2, mbId, data, comm_addr))
                     /\ I( TestAny(a1, {comms}, test_r ), AsyncReceive(a2, mbId, data, comm_addr))  


(*Two synchronization actions are independent if they concern different Mutexes and performed by different actors.*)
THEOREM \forall a1, a2 \in Actors, mt1, mt2 \in MutexIds, req1, req2, test_r \in Addresses, requests \in SUBSET MutexIds:
        /\ a1 /= a2
        /\ requests \in SUBSET  Requests[a2]
        /\ ~\E req \in requests :  req = mt1
        => /\ I(AsyncMutexLock(a1, mt1), AsyncMutexLock(a2, mt2))
           /\ I(AsyncMutexLock(a1, mt1), MutexUnlock(a2, mt2))
           /\ I(MutexUnlock(a1, mt2), MutexUnlock(a2, mt2))
           /\ I(AsyncMutexLock(a1, mt1), MutexTestAny(a2, requests, test_r))      
           /\ I(AsyncMutexLock(a1, mt1), MutexWaitAny(a2, requests))      
           /\ I(MutexUnlock(a1, mt1), MutexUnlock(a2, mt2))
           /\ I(MutexUnlock(a1, mt1), MutexWaitAny(a2, requests))
           /\ I(MutexUnlock(a1, mt1), MutexTestAny(a2, requests, test_r))

(* MutexesAsyncLock actions and MutexUnlock action are independent*)
 
THEOREM \forall a1, a2 \in Actors, mt1, mt2 \in MutexIds:
        /\ a1 /= a2 =>  I(AsyncMutexLock(a1, mt1), MutexUnlock(a2, mt2))

      
 (*Two MutexWaitAny actions, two MutexTestAny actions, a MutexWaitAny action and MutexTestAny action are independent*)             
THEOREM \forall a1, a2 \in Actors, mts1, mts2 \in SUBSET MutexIds,  test_r1, test_r2 \in Addresses:
           a1 /= a2 => 
           /\ I(MutexWaitAny(a1, mts1), MutexWaitAny(a2, mts2))
           /\ I(MutexWaitAny(a1, mts1), MutexTestAny(a2, mts2, test_r1))
           /\ I(MutexTestAny(a1, mts1, test_r1), MutexTestAny(a2, mts2, test_r2))
           
 (* A MutexesAsyncLock action and a MutexWaitAny action or MutexTestAny action are independent*)
 THEOREM \forall a1, a2 \in Actors, mt \in MutexIds, test_r \in Addresses, requests \in SUBSET MutexIds:
         a1 /= a2 =>
         /\ I(AsyncMutexLock(a1, mt), MutexWaitAny(a2, requests))
         /\ I(AsyncMutexLock(a1, mt), MutexTestAny(a1,requests , test_r))


 (* A MutexUnlock action and a MutexWaitAny action or MutexTestAny action are independent if concern different Mutexes*)
 THEOREM \forall a1, a2 \in Actors, mt \in MutexIds, test_r \in Addresses, requests \in SUBSET MutexIds:
         /\ a1 /= a2
         /\ \/ ~\E req \in requests: mt = req 
            \/ ~ twoFirstOwner(mt,a1,a2)
         =>         /\ I(MutexUnlock(a1, mt), MutexWaitAny(a2, requests))
                    /\ I(MutexUnlock(a1, mt), MutexTestAny(a1,requests , test_r))

(*A \mutexunlock~is independent of a \MutexWaitAny~or \MutexTestAny~of another actor, 
except if they concern the same Mutexes and one of the actors owns the Mutexes  ??? *)




=============================================================================
\* Modification History
\* Last modified Fri Jun 14 16:23:54 CEST 2019 by diep-chi
\* Created Thu Jun 06 11:01:30 CEST 2019 by diep-chi
