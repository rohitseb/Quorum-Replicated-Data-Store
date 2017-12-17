----------------------------- MODULE voldemort -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS N, C, STOP, ReadQ, WriteQ, FAILNUM
ASSUME N=5/\C=1/\STOP<10/\1<=ReadQ/\ReadQ<=3/\1<=WriteQ/\WriteQ<=3/\0<=FAILNUM/\FAILNUM<=2
Nodes == 1..N
Clients == N+1..N+C
(*
--algorithm voldemort{
    variable FailNum = FAILNUM,
                HVAL=0,CVAL=0,CVER=0,
                up = [n \in Nodes |-> TRUE],
                db = [n \in Nodes |-> {[ver |-> 0, val |-> 0]}];
    define
    {     
        UpNodes == {i \in 1..N : up[i]=TRUE}  
        ReturnReadQ ==  CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=ReadQ
        ReturnWriteQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=WriteQ
    }    
   
    procedure maxVal(tempQ)
    variable temp=0,x=0;
    {
         L1:while(tempQ # {}){
            x:= CHOOSE k \in tempQ: TRUE;
            tempQ:= tempQ \ {x};
            if(x>temp)
              temp:=x;            
         };
         HVAL:=temp;
         return;
    }
    
    fair process(c \in Clients)
    variable cntr = 0, hver = 0, q=0, Q ={},nodeVersions={},writeQ={},data=0,t=0,i=0,ver={},r,v=0;
    {
        CL:while(cntr<=STOP)
        {
            cntr := cntr+1;
            Q:=ReturnReadQ;
    
            L2:while(Q # {}){
              q:= CHOOSE k \in Q: TRUE;
              Q:= Q \ {q};
              ver:= db[q];
    
               L3:while(ver # {}){
                    r:= CHOOSE k \in ver: TRUE;
                    ver:= ver \ {r};
                    nodeVersions := nodeVersions \union {r.ver};
               }
            };
            
            \*get the highest version number from RQ
            call maxVal(nodeVersions);
            X1: hver:=HVAL+1;
            
           \*write val = cntr to writeQuorum with higher version number
            writeQ:=ReturnWriteQ;
    
             L4:while(writeQ # {}){
              v:= CHOOSE m \in writeQ: TRUE;
              writeQ:= writeQ \ {v};
              data:=[ver |-> hver, val |-> cntr];
              CVAL:=cntr;
              CVER:=hver;
              db[v]:=db[v]\union {data};
            }
        }
    }
    
    
    
    fair process(n \in Nodes)
    variable x=0;
    {
        L5:while(TRUE)
        {
            if(FailNum>0/\up[self]=TRUE) \*Storage node can fail
            {
                up[self]:=FALSE;
                FailNum:=FailNum-1;
            }
            else if( up[self] = FALSE)  \*Or recover
            {
                up[self]:=TRUE;
                FailNum:=FailNum+1;
            }
    }
}
}
*)
\* BEGIN TRANSLATION
\* Process variable x of process n at line 74 col 14 changed to x_
CONSTANT defaultInitValue
VARIABLES FailNum, HVAL, CVAL, CVER, up, db, pc, stack

(* define statement *)
UpNodes == {i \in 1..N : up[i]=TRUE}
ReturnReadQ ==  CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=ReadQ
ReturnWriteQ == CHOOSE i \in SUBSET(UpNodes): Cardinality(i)=WriteQ

VARIABLES tempQ, temp, x, cntr, hver, q, Q, nodeVersions, writeQ, data, t, i, 
          ver, r, v, x_

vars == << FailNum, HVAL, CVAL, CVER, up, db, pc, stack, tempQ, temp, x, cntr, 
           hver, q, Q, nodeVersions, writeQ, data, t, i, ver, r, v, x_ >>

ProcSet == (Clients) \cup (Nodes)

Init == (* Global variables *)
        /\ FailNum = FAILNUM
        /\ HVAL = 0
        /\ CVAL = 0
        /\ CVER = 0
        /\ up = [n \in Nodes |-> TRUE]
        /\ db = [n \in Nodes |-> {[ver |-> 0, val |-> 0]}]
        (* Procedure maxVal *)
        /\ tempQ = [ self \in ProcSet |-> defaultInitValue]
        /\ temp = [ self \in ProcSet |-> 0]
        /\ x = [ self \in ProcSet |-> 0]
        (* Process c *)
        /\ cntr = [self \in Clients |-> 0]
        /\ hver = [self \in Clients |-> 0]
        /\ q = [self \in Clients |-> 0]
        /\ Q = [self \in Clients |-> {}]
        /\ nodeVersions = [self \in Clients |-> {}]
        /\ writeQ = [self \in Clients |-> {}]
        /\ data = [self \in Clients |-> 0]
        /\ t = [self \in Clients |-> 0]
        /\ i = [self \in Clients |-> 0]
        /\ ver = [self \in Clients |-> {}]
        /\ r = [self \in Clients |-> defaultInitValue]
        /\ v = [self \in Clients |-> 0]
        (* Process n *)
        /\ x_ = [self \in Nodes |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "CL"
                                        [] self \in Nodes -> "L5"]

L1(self) == /\ pc[self] = "L1"
            /\ IF tempQ[self] # {}
                  THEN /\ x' = [x EXCEPT ![self] = CHOOSE k \in tempQ[self]: TRUE]
                       /\ tempQ' = [tempQ EXCEPT ![self] = tempQ[self] \ {x'[self]}]
                       /\ IF x'[self]>temp[self]
                             THEN /\ temp' = [temp EXCEPT ![self] = x'[self]]
                             ELSE /\ TRUE
                                  /\ temp' = temp
                       /\ pc' = [pc EXCEPT ![self] = "L1"]
                       /\ UNCHANGED << HVAL, stack >>
                  ELSE /\ HVAL' = temp[self]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
                       /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
                       /\ tempQ' = [tempQ EXCEPT ![self] = Head(stack[self]).tempQ]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << FailNum, CVAL, CVER, up, db, cntr, hver, q, Q, 
                            nodeVersions, writeQ, data, t, i, ver, r, v, x_ >>

maxVal(self) == L1(self)

CL(self) == /\ pc[self] = "CL"
            /\ IF cntr[self]<=STOP
                  THEN /\ cntr' = [cntr EXCEPT ![self] = cntr[self]+1]
                       /\ Q' = [Q EXCEPT ![self] = ReturnReadQ]
                       /\ pc' = [pc EXCEPT ![self] = "L2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << cntr, Q >>
            /\ UNCHANGED << FailNum, HVAL, CVAL, CVER, up, db, stack, tempQ, 
                            temp, x, hver, q, nodeVersions, writeQ, data, t, i, 
                            ver, r, v, x_ >>

L2(self) == /\ pc[self] = "L2"
            /\ IF Q[self] # {}
                  THEN /\ q' = [q EXCEPT ![self] = CHOOSE k \in Q[self]: TRUE]
                       /\ Q' = [Q EXCEPT ![self] = Q[self] \ {q'[self]}]
                       /\ ver' = [ver EXCEPT ![self] = db[q'[self]]]
                       /\ pc' = [pc EXCEPT ![self] = "L3"]
                       /\ UNCHANGED << stack, tempQ, temp, x >>
                  ELSE /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "maxVal",
                                                                   pc        |->  "X1",
                                                                   temp      |->  temp[self],
                                                                   x         |->  x[self],
                                                                   tempQ     |->  tempQ[self] ] >>
                                                               \o stack[self]]
                          /\ tempQ' = [tempQ EXCEPT ![self] = nodeVersions[self]]
                       /\ temp' = [temp EXCEPT ![self] = 0]
                       /\ x' = [x EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "L1"]
                       /\ UNCHANGED << q, Q, ver >>
            /\ UNCHANGED << FailNum, HVAL, CVAL, CVER, up, db, cntr, hver, 
                            nodeVersions, writeQ, data, t, i, r, v, x_ >>

L3(self) == /\ pc[self] = "L3"
            /\ IF ver[self] # {}
                  THEN /\ r' = [r EXCEPT ![self] = CHOOSE k \in ver[self]: TRUE]
                       /\ ver' = [ver EXCEPT ![self] = ver[self] \ {r'[self]}]
                       /\ nodeVersions' = [nodeVersions EXCEPT ![self] = nodeVersions[self] \union {r'[self].ver}]
                       /\ pc' = [pc EXCEPT ![self] = "L3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L2"]
                       /\ UNCHANGED << nodeVersions, ver, r >>
            /\ UNCHANGED << FailNum, HVAL, CVAL, CVER, up, db, stack, tempQ, 
                            temp, x, cntr, hver, q, Q, writeQ, data, t, i, v, 
                            x_ >>

X1(self) == /\ pc[self] = "X1"
            /\ hver' = [hver EXCEPT ![self] = HVAL+1]
            /\ writeQ' = [writeQ EXCEPT ![self] = ReturnWriteQ]
            /\ pc' = [pc EXCEPT ![self] = "L4"]
            /\ UNCHANGED << FailNum, HVAL, CVAL, CVER, up, db, stack, tempQ, 
                            temp, x, cntr, q, Q, nodeVersions, data, t, i, ver, 
                            r, v, x_ >>

L4(self) == /\ pc[self] = "L4"
            /\ IF writeQ[self] # {}
                  THEN /\ v' = [v EXCEPT ![self] = CHOOSE m \in writeQ[self]: TRUE]
                       /\ writeQ' = [writeQ EXCEPT ![self] = writeQ[self] \ {v'[self]}]
                       /\ data' = [data EXCEPT ![self] = [ver |-> hver[self], val |-> cntr[self]]]
                       /\ CVAL' = cntr[self]
                       /\ CVER' = hver[self]
                       /\ db' = [db EXCEPT ![v'[self]] = db[v'[self]]\union {data'[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "L4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CL"]
                       /\ UNCHANGED << CVAL, CVER, db, writeQ, data, v >>
            /\ UNCHANGED << FailNum, HVAL, up, stack, tempQ, temp, x, cntr, 
                            hver, q, Q, nodeVersions, t, i, ver, r, x_ >>

c(self) == CL(self) \/ L2(self) \/ L3(self) \/ X1(self) \/ L4(self)

L5(self) == /\ pc[self] = "L5"
            /\ IF FailNum>0/\up[self]=TRUE
                  THEN /\ up' = [up EXCEPT ![self] = FALSE]
                       /\ FailNum' = FailNum-1
                  ELSE /\ IF up[self] = FALSE
                             THEN /\ up' = [up EXCEPT ![self] = TRUE]
                                  /\ FailNum' = FailNum+1
                             ELSE /\ TRUE
                                  /\ UNCHANGED << FailNum, up >>
            /\ pc' = [pc EXCEPT ![self] = "L5"]
            /\ UNCHANGED << HVAL, CVAL, CVER, db, stack, tempQ, temp, x, cntr, 
                            hver, q, Q, nodeVersions, writeQ, data, t, i, ver, 
                            r, v, x_ >>

n(self) == L5(self)

Next == (\E self \in ProcSet: maxVal(self))
           \/ (\E self \in Clients: c(self))
           \/ (\E self \in Nodes: n(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(c(self)) /\ WF_vars(maxVal(self))
        /\ \A self \in Nodes : WF_vars(n(self))

\* END TRANSLATION

Termination == <> (CVER=STOP)
invariant == CVER=CVAL

=============================================================================


The code given above is an implementation of the Voldermort single copy consistency.

The invariant we have specified in the above code is that the value of the version number and the value of the data written in a round is the same.
In the ideal case with perfect copy consistency, the value of the version number and data should be the same.

Given below are the results we got for some of the values of ReadQ, WriteQ and FAILNUM that we tested our system on

Case 1: When ReadQ = 1, WriteQ=1 and FAILNUM =0

This is the ideal case where no node fails and the system runs without any hiccups. Our system runs successfully for this case satisfiying the invariant. 
The same result can be expected for higher values of ReadQ and WriteQ with FailNum remaining as 0.

Case 2: When ReadQ = 1, WriteQ=1 and FAILNUM =1

The system fails in this case as the invariant property is violated ie the value of the version number and the value of the data entered is not the same.

Case 3: When ReadQ = 2, WriteQ=1 and FAILNUM =1

The system fails for this case too as the invariant property is violated.

Case 4: When ReadQ = 1, WriteQ=2 and FAILNUM =1

The system fails for this case too as the invariant property is violated.

Case 5: When ReadQ = 2, WriteQ=2 and FAILNUM =1

The system runs to completion in this configuration of ReadQ, WriteQ and FAILNUM.

Case 6: When ReadQ = 3, WriteQ=2 and FAILNUM =2

The system fails for this case as the invariant property is violated.

Case 7: When ReadQ = 2, WriteQ=3 and FAILNUM =2

The system fails for this case as the invariant property is violated.

Case 8: When ReadQ = 3, WriteQ=3 and FAILNUM =2

The system runs to completion in this configuration of ReadQ, WriteQ and FAILNUM.

From the analysis we have done above we have come to the conclusion that the value of ReadQ and WriteQ should be one greater than FAILNUM. This will ensure that
at a time the most current value written to the database will always be present in a node that has not failed. This will ensure single copy consistency.

Note - The initial value of defaultInitValue should be given as 0 or as the model value 








