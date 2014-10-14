----------------------------- MODULE fmk -----------------------------
EXTENDS Naturals, Sequences
CONSTANTS 	DC,		\* Set of all DataCenters
 			Pha,	\* Set of all Pharmacies
 			Pat,	\* Set of all Patients
 			Tre,	\* Set of all Treatments
 			Pre,	\* Set of all Prescriptions
 			Doc,    \* Set of all Doctors
 			MAX     \* maximun clock

VARIABLE patientdb, clock

ASSUME MAX \in Nat


TimeStamps == DC \times (1..MAX)

\* Initialize Variables
Init == 
	/\ patientdb = [d \in DC |-> [ p \in Pat |-> [treat |-> {}, 
								                  presc |-> {},
								                  taken |-> {} ] ] ]
	/\ clock = [ d \in DC |-> 0 ]


\* Local Operation at the datacenter d that represents adding a treatment t to patient p by doctor doc 
\* Pre:		- doc, p, t all exist and belong to their set.
\* Post:	- The patient p treatment t is updated in the local DC d.
\*			- The logical clock is incremented by one.

addTreatment(dc, patient, doctor, treatment) ==
	LET 
		timestamp == << dc, clock[dc] + 1 >>
		s == patientdb[dc]
		t == << doctor, treatment, timestamp >>
	IN
		/\ patientdb' = [ patientdb EXCEPT ![dc][patient].treat = s[patient].treat \cup {t} ]
		/\ clock' = [clock EXCEPT ![dc] = clock[dc] + 1]



\* Local Operation at the datacenter d that represents adding a prescription pres to the treatment <<doc, t, date>>
\* Pre:		- doc, pres, t all exist and belong to their set.
\* Post:	- If the <<doc, t, date>> exists it adds a the prescription.

addPrescription(dc, patient, doctor, treatment, timestamp, prescription) == 
	LET 
		p == << doctor, treatment, timestamp, prescription>>
		s == patientdb[dc]
	IN
	    /\ << doctor, treatment, timestamp >> \in s[patient].treat
        /\ p \notin s[patient].presc
        /\ patientdb' = [patientdb EXCEPT ![dc][patient].presc = s[patient].presc \cup {p} ]
		/\ UNCHANGED<<clock>>

\* Local Operation at the datacenter d that represents consuming a prescription pres in a pharmacy f by a patient p
\* Pre:		- f, p, pres all exists and belongs to their set.
\* Post: 	- 

giveDrug(dc, patient, doctor, treatment, timestamp, prescription, pharmacy) ==
	LET
        timestamp2 == << dc, clock[dc] + 1 >>
        p ==  << doctor, treatment, timestamp, prescription, pharmacy, timestamp2 >>
		s == patientdb[dc]
	IN
		/\ << doctor, treatment, timestamp, prescription>> \in s[patient].presc
        /\ \E ts \in TimeStamps : << doctor, treatment, timestamp, prescription, pharmacy, ts >> \in s[patient].taken
        /\ patientdb' = [ patientdb EXCEPT ![dc][patient].taken = s[patient].taken \cup {p} ]
		/\ clock' = [clock EXCEPT ![dc] = clock[dc] + 1]


\* Merge two datacenter databases
merge(dc1, dc2) ==
    LET 
        s1 == patientdb[dc1]
        s2 == patientdb[dc2]
        ns == [ p \in Pat |-> [treat |-> s1[p].treat \cup s2[p].treat, 
                                presc |-> s1[p].presc \cup s2[p].presc,
                                taken |-> s1[p].taken \cup s2[p].taken ] ]
    IN
        /\ patientdb' = [ patientdb EXCEPT ![dc1] = ns, ![dc2] = ns]
        /\ UNCHANGED<<clock>>

NoDrugGivenTwice == \A d \in DC : \E p \in Pat: \E t1 \in patientdb[d][p].taken, t2 \in patientdb[d][p].taken :
    t1 /= t2 /\ SubSeq(t1, 1, 5) =  SubSeq(t2, 1, 5)     \*  DO NOT HOLD	
	
Next == 
    \/ \E dc \in DC, patient \in Pat, doctor \in Doc, treatment \in Tre : addTreatment(dc,patient,doctor,treatment) 
    \/ \E dc \in DC, patient \in Pat, doctor \in Doc, treatment \in Tre, ts \in TimeStamps, prescription \in Pre : 
            addPrescription(dc,patient,doctor,treatment,ts,prescription) 
    \/ \E dc \in DC, patient \in Pat, doctor \in Doc, treatment \in Tre, ts \in TimeStamps, prescription \in Pre, pharmacy \in Pha : 
            giveDrug(dc,patient,doctor,treatment,ts,prescription,pharmacy)         
    
Spec == Init /\ [][Next]_<<patientdb,clock>>

THEOREM Spec => []NoDrugGivenTwice \*This has to be defined
=============================================================================