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
                   
  - A state is represented by 4 variables: Communications, memory, pc, Mutexes and MtRequests
    + Communications is the set of all communications in the system
    + memory is indexed by Actors' id, memory[Aid] is used to store id of communications, id of MtRequests, values of local vairables 
    + pc is indexed by id of Actors, pc[Aid] represents the program counter of actor Aid, changed  after firing each action 
    + waitinQueue is indexed by mutexes, Mutexes[mid] is a fifo queue that remembers which actors have required it
    + MtRequests is indexed by Actors' id, MtRequests[Aid] is the set of all the mutex ids requested by the actor Aid   
   
  - Actions are structured in 3 subsystems:
    - the Local actions :  Local, 
    - the Communication actions: AsyncSend, AsyncReceive, Wait, Test,
    - the Synchronization actions: MutexAsyncLock, MutexUnLock, MutexTest and MutexWait.
   *)
   
(*---------------------------- GENERAL CONSTANTS, VARIABLES, FUNCTIONS  --------------------------------------------*)
    
EXTENDS Integers , Naturals, Sequences, FiniteSets

CONSTANTS (* Sets containing the names of all the actors, mailboxes and mutexes *)
          ActorsIds, MailboxesIds, MutexesIds,
         (* Set of all existing memory addresses. Each actor has its own private memory, indexed by these addresses *)
          Addresses,
         (* The test action writes a boolean in memory *)
         ValTrue, ValFalse,
          (* Existing Actions Types *)
         SendIns, ReceiveIns, WaitIns, TestIns, LocalIns, LockIns, UnlockIns,  MwaitIns, MtestIns
          
VARIABLES Communications, (* Set of all ongoing comm MtRequests.  *)
          memory, pc,  Mutexes, MtRequests, Mailboxes, comId

NoActor == CHOOSE p : p \notin ActorsIds
NoAddr == CHOOSE a : a \notin Addresses

ASSUME ValTrue \in Nat
ASSUME ValFalse \in Nat

Partition(S) == \forall x,y \in S : x \cap y /= {} => x = y
ASSUME Partition({SendIns, ReceiveIns, WaitIns, TestIns, LocalIns , LockIns, UnlockIns, MwaitIns, MtestIns}) 

Instr ==UNION {SendIns, ReceiveIns, WaitIns, TestIns, LocalIns ,LockIns, UnlockIns, MwaitIns, MtestIns}


(* Initially there are no Communications, no MtRequests on the mutexes, memory has random values *)

Init == /\ Communications = {}
        (*/\ memory \in [ActorsIds -> [Addresses -> Nat]*)
        
        (*Set memory for running model*)
        /\ memory \in [ActorsIds -> [Addresses -> {0}]]
        
        /\ Mutexes = [i \in MutexesIds |-> <<>>] 
        /\ Mailboxes = [i \in MailboxesIds |-> {}] 
        
        /\ MtRequests = [i \in ActorsIds |-> {}]
        (*/\ pc = CHOOSE f \in [ActorsIds -> Instr] : TRUE*)
        /\ pc = [a \in ActorsIds |-> "lock"] 
        /\ comId = 0




(* Comm type is declared as a structure *)  
Comm == [id:Nat,
         status:{"send", "receive","done"},
         src:ActorsIds,
         dst:ActorsIds,
         data_src:Addresses,
         data_dst:Addresses]

(* Let's keep everything in the right domains, just for checking *)
TypeInv == /\ \forall c \in Communications : c \in Comm  /\ c.status = "done"
           /\ \forall mbId \in MailboxesIds: \forall c \in Mailboxes[mbId]: c \in Comm  /\ \/ c.status = "send" 
                                                                                           \/ c.status = "receive" 
           /\ \forall mid \in MutexesIds: \forall id \in Mutexes[mid]: id \in ActorsIds

           /\ memory \in [ActorsIds -> [Addresses -> Nat]]
           /\ pc \in [ActorsIds -> Instr] 


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


(* A local computaion of Actor <Aid> can change the value of this Actor's memory at any address, 
    but not where communications data  are strored      *)

Local(Aid) ==
    /\ Aid \in ActorsIds
    /\ pc[Aid] \in LocalIns
    
    \*change value of memory[Aid][a], set {0,1,2,3,4,5} just for running model
    /\ memory' \in [ActorsIds -> [Addresses -> Nat]]
    /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
    /\ UNCHANGED <<Communications, Mutexes, MtRequests, Mailboxes, comId >>


(* ---------------------------------------------COMMUNICATION SUBSYSTEM -----------------------------------*)

(* AsyncSend(Aid,mb,data_addr,comm_addr):  
    the actor <Aid> sends a "send" request to the maibox <mb>. 
    If a pending "receive" request already exists, they are combined to create a "ready" communication in the set Communications, 
    otherwise a new communication with "send" status is created,
    address <data_addr> of Actor <Aid> contains the data to transmit,
    and memory address <comm_addr> of Actor <Aid> is assigned the id of the communication 

  Parameters:
    - Aid: the Actor ID of the sender 
    - mb: the mailbox where the "send" communication request is pushed 
    - data_addr: the address in the AsyncSender's memory where the data to transmit is stored 
    - comm_addr: the address in the AsyncSender's memory where to store the communication id *)

AsyncSend(Aid, mb, data_addr, comm_addr) == 
  /\ Aid \in ActorsIds
  /\ mb \in MailboxesIds
  /\ data_addr \in Addresses
  /\ comm_addr \in Addresses
  /\ pc[Aid] \in SendIns
   
     (* If a matching "receive" request exists in the mailbox(mb), choose the oldest one and
        complete the Sender fields and set the communication to the "ready" state *)
  /\ \/ \exists request \in Mailboxes[mb]:
          /\ request.status="receive"
          /\ \forall d \in Mailboxes[mb]: d.status="receive" => request.id <= d.id
          /\ Communications' = 
             Communications   \cup {[request EXCEPT
                                       !.status = "done",
                                       !.src = Aid,
                                       !.data_src = data_addr]}
          /\ Mailboxes' = [Mailboxes EXCEPT ![mb] = Mailboxes[mb] \ {request}]
          /\ memory' = [memory EXCEPT ![request.dst][request.data_dst] = memory[request.src][request.data_src]]
          /\ memory' = [memory EXCEPT ![Aid][comm_addr] = request.id] 
          /\ UNCHANGED <<comId>>    
               
     
     (* Otherwise (i.e. no matching AsyncReceive communication request exists,
        create a AsyncSend request and push it in the set Communications. *)
     \/ /\ ~ \exists req \in Mailboxes[mb]: req.status = "receive" 
        /\ LET request ==  
                 [id |-> comId, 
                  status |-> "send", 
                  src |-> Aid,
                  dst |-> NoActor,  (* destination is randomly chosen ? *) 
                  data_src |-> data_addr,
                  data_dst |-> NoAddr]
           IN
             /\ Mailboxes' = [Mailboxes EXCEPT ![mb] = Mailboxes[mb] \cup {request}]
             /\ memory' = [memory EXCEPT ![Aid][comm_addr] = request.id] 
             /\ UNCHANGED <<Communications>>    
             /\ comId' = comId+1
  (* AsyncSend is never blocking *)             
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED << Mutexes, MtRequests>>
  
 
 
(* AsyncReceive(Aid,mb,data_addr,comm_addr): the actor <Aid> sends a "receive" request to the mailbox <mb>.
   If there is a pending "send" request on the same mailbox <mb>, they are combined to create a "ready" communication, 
   otherwise a new communication is created with "receive" status.
   the address <data_addr> 
   the address <comm_addr> of <Aid> is assigned the id of the communication,
   
  Parameters: 
    - Aid: the Actor ID of the receiver 
    - mb: the mailbox where the "receive" communication request is going to be pushed 
    - data_addr: the address in the receivers's memory where the data is going to be stored 
    - comm_addr: the address in the receivers's memory where to store the communication id *)

AsyncReceive(Aid, mb, data_addr, comm_addr) == 
  /\ Aid \in ActorsIds
  /\ mb \in MailboxesIds
  /\ data_addr \in Addresses
  /\ comm_addr \in Addresses
  /\ pc[Aid] \in ReceiveIns
 
     (* If a matching "send" request exists in the mailbox mb, choose the oldest one and,
        complete the receiver's fields and set the communication to the "ready" state *)
  /\ \/ \exists request \in Mailboxes[mb]:
          /\ request.status="send"
          /\ \forall d \in Mailboxes[mb]: d.status="send" => request.id <= d.id
          /\ Communications' = 
             Communications  \cup {[request EXCEPT
                                       !.status = "done",
                                       !.dst = Aid,
                                       !.data_dst = data_addr
                                        ]}
          /\ memory' = [memory EXCEPT ![request.dst][request.data_dst] = memory[request.src][request.data_src]]
          /\ Mailboxes' = [Mailboxes EXCEPT ![mb] = Mailboxes[mb] \ {request}]
          /\ memory' = [memory EXCEPT ![Aid][comm_addr] = request.id]
          /\ UNCHANGED <<comId>>    
               
     (* Otherwise (i.e. no matching AsyncSend communication request exists),  
        create a "receive" request and push it in the Communications. *)
     \/ /\ ~ \exists req \in Mailboxes[mb]: req.status = "send" 
        /\ LET request ==  
                 [id |-> comId,
                  status |-> "receive", 
                  src |-> NoActor,
                  dst |-> Aid, 
                  data_src |-> NoAddr,
                  data_dst |-> data_addr]
           IN
             /\ Mailboxes' = [Mailboxes EXCEPT ![mb] = Mailboxes[mb] \cup {request}]
             /\ memory' = [memory EXCEPT ![Aid][comm_addr] = request.id]
             /\ UNCHANGED <<Communications>>    
             /\ comId' = comId+1
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests >>

(* Wait(Aid,comm_addrs):  Actor <Aid> waits for at least one communication from a given set <comm_addrs> to complete 
    If the communication is "ready" for being processed, data is transfered from the source actor to the destination actor, 
    from/to the addresses specified in the communication, 
       if it is already "done", there is nothing to do.
    The function is blocking when no communication is "ready" or "done".   
 Parameters:
    - Aid: the Actor's ID issuing the wait request
    - comm_addrs: the list of addresses in the Actor's memory where the communication ids are stored 
*)

WaitAny(Aid, comm_addrs) ==
  /\ Aid \in ActorsIds
  /\ pc[Aid] \in WaitIns
  /\ \E comm_addr \in comm_addrs, c \in Communications: c.id = memory[Aid][comm_addr]
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests, Mailboxes, comId, memory, Communications >>
 (* otherwise i.e. no communication in <comm_addrs> is "ready" or "done", WaitAny is blocking *)



(* Test(Aid, comm_addrs, ret_r): Actor <Aid> waits for at least one communication from a given list <comm_addrs> to complete,
    and returns the boolean result at memory adress <ret_r>.
    The function is very similar to Wait, but returns ret_r as a result, and is never blocking.
    Parameters
    - Aid: the Actor ID issuing the test request 
    - comm_addrs: the list of addresses in the Actor's memory where the communication ids are stored 
    - ret_r: the address in the Actor memory where the boolean result is going to be stored *)

TestAny(Aid, comm_addrs, ret_r) ==
  /\ Aid \in ActorsIds
  /\ ret_r \in Addresses
  /\ pc[Aid] \in TestIns
  /\ \/ \E comm_addr \in comm_addrs, c\in Communications: c.id = memory[Aid][comm_addr] /\
        (* If the communication is "done" return ValTrue *)
           /\ c.status = "ready"
           /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValTrue]
        (* if no communication is "done", return ValFalse *)   
     \/ ~ \exists comm_addr \in comm_addrs, c \in Communications: c.id = memory[Aid][comm_addr]
        /\ c.status = "done"
        /\ memory' = [memory EXCEPT ![Aid][ret_r] = ValFalse]
        /\ UNCHANGED <<Communications>> 
  (* Test is non-blocking since in all cases pc[AId] is incremented *)
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests, Mailboxes, comId>>
  

(* -------------------------------- SYNCHRONIZATION SUBSYSTEM ----------------------------------------------------*)
                                
(* MutexAsyncLock(Aid, mid, req_a) : Actor <Aid> is requesting a lock on mutex <mid>. If allowed, address <req_a> stores the mutex id <mid>.    
- If the actor <Aid> has no pending request on mutex <mid>, a new one is created 
        - add pair [mid,req_a] in Request[Aid]
        - store <mid> in memory[Aid][req_a], i.e. local address <req_a> is assigned value <mid>
        - enqueue <Aid> in Mutexes[mid]
 The operation is non-blocking (pc[Aid] is modified in any case)       
*) 
 
 
 MutexAsyncLock(Aid, mid, req_addr) ==
   /\ Aid \in ActorsIds
   /\ pc[Aid] \in LockIns
   /\ mid \in MutexesIds
   /\ req_addr \in Addresses
         (* if Actor <Aid> has no pending request on mutex <mid>, create a new one *)      
   /\ \/ /\ ~isMember(Aid, Mutexes[mid])
         /\  MtRequests'  = [MtRequests EXCEPT ![Aid]= MtRequests[Aid] \cup {mid}]
         /\  memory' = [memory EXCEPT ![Aid][req_addr] = mid]  
         /\ Mutexes' = [Mutexes EXCEPT ![mid] = Append(Mutexes[mid], Aid)]
         (* otherwise i.e. actor <Aid> alreadly has a pending request on mutex <mid>, keep the variables unchanged *)          
      \/ /\ isMember(Aid, Mutexes[mid]) 
         /\ UNCHANGED <<Mutexes,  memory, MtRequests>>  
   (* MutexAsyncLock is never blocking, in any case, pc[Aid] is incremented *) 
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   /\ UNCHANGED <<Communications, Mailboxes, comId>>
       
  
  
(* MutexUnlock(Aid, mid): the Actor <Aid> wants to release the mutex <mid>
    A "valid" unlock occurs when <Aid> is in Mutexes[mid] 
    - it is either a normal unlock when <Aid> owns <mid> (it is head of Mutexes[mid]) 
    - or a cancel otherwise. 
    In both cases all links between <mid> and <Aid> are removed in Mutexes[mid] and MtRequests[Aid] 
   An "invalid" unlock occurs when <Aid> is not in Mutexes[mid]    
     that's not enabled, and in this case <Aid> is blocked (pc[Aid] is not modified in this case).
 *)
 
MutexUnlock(Aid, mid) ==
   /\ Aid \in ActorsIds
   /\ mid \in MutexesIds
   /\ pc[Aid] \in UnlockIns
   
   (* If <Aid> makes a "valid" unlock on <mid> (either owner or not) remove any linking between them *)
   /\ isMember(Aid, Mutexes[mid]) 
   /\ Mutexes' = [Mutexes EXCEPT ![mid] = remove(Aid,Mutexes[mid])]
   /\ MtRequests' = [MtRequests EXCEPT ![Aid] = MtRequests[Aid] \ {mid }]
   /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
   /\ UNCHANGED <<memory, Communications, Mailboxes, comId>>
   
   (* Otherwise, the transition is not enabled and Actor <Aid> is blocked *)
   
   
(* MutexWait(Aid, req_addr): Actor <Aid> waits for lock request <req_a>, 
  - if there is a req in Request[Aid] whose mid is <req_a>, and <Aid> is the owner of this mutex mid (head of Mutexes[req.id]), 
    then MutexWait is enabled
  - otherwise the transition is not enabled.
  MutexWait is thus blocking until <Aid> owns the mutex 
 *)

MutexWait(Aid, req_addr) == 
/\ Aid \in ActorsIds
/\ req_addr \in Addresses
/\ pc[Aid] \in MwaitIns
    (* If req_a is the id of a Request of Actor <Aid>, and <Aid> is the owner of this mutex, <Aid> proceeds and increment its pc *) 
/\ \E req \in MtRequests[Aid]: req = memory[Aid][req_addr] /\ isHead(Aid, Mutexes[req])
/\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
/\ UNCHANGED << memory, Mutexes, MtRequests, Communications, Mailboxes, comId>>

(* otherwise <Aid> is blocked, pc[Aid] is unmodified *)  


(* MutexTest(Aid,req_addr, result_addr): actor <Aid> tests if he is the owner of the mutex of mid <req_a> 
            (i.e. he is the head of the mutex Mutexes)
            and stores the boolean result at address <tesr_a> 
            MutexTest is non-blocking (in any case pc[Aid] is modified).
            *)
MutexTest(Aid, req_addr,result_addr) ==
  /\ Aid \in ActorsIds
  /\ pc[Aid] \in MtestIns
  /\ result_addr \in Addresses
  /\  \E req \in  MtRequests[Aid]: req = memory[Aid][req_addr]/\ 
       (* If the actor is the owner then return true *)
        \/ /\ isHead(Aid,Mutexes[req])
           /\ memory' = [memory EXCEPT ![Aid][result_addr] = ValTrue]
       (*else if it is not the onwer then return false *)
        \/ /\ ~isHead(Aid, Mutexes[req])
           /\ memory' = [memory EXCEPT ![Aid][result_addr] = ValFalse] 
  /\ \E ins \in Instr : pc' = [pc EXCEPT ![Aid] = ins]
  /\ UNCHANGED <<Mutexes, MtRequests, Communications,  Mailboxes, comId>>


--------------------------------------------------------------------------------------------------------------------------------
                                    (*INDICATE NEXT ACTIONS *)
                                    
(* Next indicates the possible actions that could be fired at a state  *)
Next == \exists actor \in ActorsIds, data_addr \in Addresses, comm_addr \in Addresses, req \in Addresses, result_addr \in Addresses, comm_addrs \in SUBSET Addresses, mb \in MailboxesIds ,
                result_addr1 \in Addresses, ids \in SUBSET Communications, mutex \in MutexesIds:
          \/ AsyncSend(actor, mb, data_addr, comm_addr)
          \/ AsyncReceive(actor, mb, data_addr, comm_addr)
          \/ WaitAny(actor, comm_addrs)
          \/ TestAny(actor, comm_addrs, result_addr)
          \/ Local(actor) 
          \/ MutexAsyncLock(actor,mutex,req)
          \/ MutexWait(actor, req)
          \/ MutexTest(actor,req, result_addr1) 
          \/ MutexUnlock(actor,mutex)
          
 
Spec == Init /\ [][Next]_<< pc, Communications, memory, Mutexes, MtRequests, Mailboxes, comId >>
-----------------------------------------------------------------------------------------------------------------

(* Definition of the Independence relation *)
I(A,B) == ENABLED A /\ ENABLED B => /\ A => (ENABLED B)'
                                    /\ B => (ENABLED A)'
                                    /\ A \cdot B \equiv B \cdot A

-----------------------------------------------------------------------------------------------------------------
(* ------------------------- INDEPENDENCE THEOREMS --------------------------------------------------------------*)

(* Independence theorems for Communications *)

(* AsyncSend and AsyncReceive are always independent *)
THEOREM \forall a1, a2 \in ActorsIds: \forall mb1, mb2 \in MailboxesIds: 
        \forall data1, data2, comm1, comm2 \in Addresses:
        (* /\ a1 /= a2   this is not necessary  since if identical, they cannot be both enabled *)
        (* those hypothesis are not necessary since enabledness is already in the definition on independence 
          /\ ENABLED AsyncSend(a1, mb1, data1, comm1)                      
          /\ ENABLED AsyncReceive(a2, mb2, data2, comm2) 
          *)
      TRUE  =>  I(AsyncSend(a1, mb1, data1, comm1), 
              AsyncReceive(a2, mb2, data2, comm2))

(* AsyncSend and Wait are independent when they concern different communications *)
(* !!! Unsure about conditions for independence *)

THEOREM \forall a1, a2 \in ActorsIds: \forall data, comm1, comm2 \in Addresses:
        \forall mb \in MailboxesIds: \exists c \in Communications:
        /\ a1 /= a2        (* a1 and a2 are different Actors *)
        /\ c.id = memory[a2][comm2]                          (*  c is the communication with id comm2 *)
        /\ \/ (a1 /= c.dst /\ a1 /= c.src)                   (*  either a1 is neither src nor dst of c *)
           \/ (comm1 /= c.data_src /\ comm1 /= c.data_dst)   (*  or     comm1 is neither src or dst addr of c *) 
        (*  /\ ENABLED AsyncSend(a1, mb, data, comm1) 
            /\ ENABLED Wait(a2, comm2) 
            *)
         =>  I(AsyncSend(a1, mb, data, comm1), WaitAny(a2, comm2)) 

(* !!!!! Similar theorems should hold for AsyncSend and Test, AsyncReceive and Wait, AsyncReceive and Test *)
(* to be done ... *)


(* two AsyncSend are independent if they concern (different processes and) different mailboxes *)
THEOREM \forall a1, a2 \in ActorsIds: \forall mb1, mb2 \in MailboxesIds: 
        \forall data1, data2, comm1, comm2 \in Addresses:
        (* /\ a1 /= a2   this is unnecessary since they would not be both enabled if equal *)
        /\ mb1 /= mb2
        (* /\ ENABLED AsyncSend(a1, mb1, data1, comm1) 
           /\ ENABLED AsyncSend(a2, mb2, data2, comm2)  
           *)
        => I(AsyncSend(a1, mb1, data1, comm1),
             AsyncSend(a2, mb2, data2, comm2))
(* two AsyncReceive are independent if thy concern (different processes and) different mailboxes *)
THEOREM \forall a1, a2 \in ActorsIds: \forall mb1, mb2 \in MailboxesIds: 
        \forall data1, data2, comm1, comm2 \in Addresses:
        (* /\ a1 /= a2  *)
        /\ mb1 /= mb2
        (* /\ ENABLED AsyncReceive(a1, mb1, data1, comm1)
           /\ ENABLED AsyncReceive(a2, mb2, data2, comm2) 
           *)
        => I(AsyncReceive(a1, mb1, data1, comm1),
             AsyncReceive(a2, mb2, data2, comm2))


(* two Wait actions are always independent  *)
THEOREM \forall a1, a2 \in ActorsIds: \forall comm_addrs1, comm_addrs2 \in SUBSET Addresses:
        (* /\ a1 /= a2 *)
       (* /\ comm1 = comm2
        /\ ENABLED Wait(a1, comm1)
        /\ ENABLED Wait(a2, comm2) *)
      TRUE => I(WaitAny(a1, comm_addrs1), WaitAny(a2, comm_addrs2))
      
(* two Test actions are always independent  *)
THEOREM \forall a1, a2 \in ActorsIds: \forall comm_addrs1, comm_addrs2 \in SUBSET Addresses: \forall test_r1, test_r2 \in Addresses:
        (* /\ a1 /= a2 *)
       (* /\ comm1 = comm2
        /\ ENABLED Wait(a1, comm1)
        /\ ENABLED Wait(a2, comm2) *)
      TRUE => I(TestAny(a1, comm_addrs1,test_r1), TestAny(a2, comm_addrs2, test_r2))   
      
(* a Test and a Wait are always independent  *)
THEOREM \forall a1, a2 \in ActorsIds: \forall comm_addrs1, comm_addrs2 \in SUBSET Addresses: \forall test_r  \in Addresses:
        (* /\ a1 /= a2 *)
       (* /\ comm1 = comm2
        /\ ENABLED Wait(a1, comm1)
        /\ ENABLED Wait(a2, comm2) *)
      TRUE => I(TestAny(a2, comm_addrs2, test_r),WaitAny(a1, comm_addrs1)) 
              
      
         
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
\* Last modified Fri Jun 22 17:39:11 CEST 2018 by diep-chi
\* Created Fri Jan 12 18:32:38 CET 2018 by diep-chi
