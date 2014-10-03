----------------------------- MODULE fmk -----------------------------
EXTENDS Naturals
CONSTANTS 	DC,		\* Set of all DataCenters
 			Phar,	\* Set of all Pharmacies
 			Pat,	\* Set of all Patients
 			Tre,	\* Set of all Treatments
 			Pres	\* Set of all Prescriptions

VARIABLE patientdb, clock


Init == 
	/\ patientdb = [ p \in Pat |-> [treat |-> {}, 
								presc |-> {},
								taken |-> {} ]
								]
	/\ clock = [d \in DC |-> 0 ]



\* Local Operation at the datacenter d that represents adding a treatment t to patient p by doctor doc 
\* Pre:		- doc, p, t all exist and belong to their set.
\* Post:	- The patient p treatment t is updated in the local DC d.
\*			- The logical clock is incremented by one.

addTreatment(d, doc, p, t) ==
	LET 
		date == clock[d]+1
		s == patientdb[d]
		treatment == <<doc, p, date>>
		ns == [ treat |-> s[p].treat \cup {treatment}]
	IN
		/\ patientdb' = [ patientdb EXCEPT ![d][p] = ns]
		/\ clock' = [clock EXCEPT ![d] = date]



\* Local Operation at the datacenter d that represents adding a prescription pres to the treatment <<doc, t, date>>
\* Pre:		- doc, pres, t all exist and belong to their set.
\* Post:	- If the <<doc, t, date>> exists it adds a the prescription.

addPrescription(dc, doctor, treatment, date, prescription, patient) == 
	LET 
		p == << doctor, treatment, date, prescription>>
		s == patientdb[dc]

		ns == [ treat |-> s[patient].treatment, \* Use this to check is the same treatment, or that it exists
			   presc |-> {p} \cup s[patient].prescription,
			   taken |-> s[patient].taken
			 ]
	IN
	    /\ <<doctor, treatment, date>> \in s[patient].treatment
		/\ patientdb' = [patientdb EXCEPT ![dc][patient] = ns]

\* Local Operation at the datacenter d that represents consuming a prescription pres in a pharmacy f by a patient p
\* Pre:		- f, p, pres all exists and belongs to their set.
\* Post: 	- 

giveDrug(dc, pharmacy, patient, doctor, treatment, date, prescription) ==
	LET
	    p ==  << doctor, treatment, date, prescription, pharmacy>>
		s == patientdb[dc]
		ns == [	treat |-> s[patient].treat,
				presc |-> s[patient].presc,
				taken |-> {p} \cup s[patient].taken
			]
	IN
		patientdb' = [ patientdb EXCEPT ![dc][patient] = ns ]


Consistency == TRUE \*This has to be defined
	
Next == <<patientdb>>

Spec == Init /\ [][Next]_<<patientdb,clock>>

THEOREM Spec => TRUE \*This has to be defined
=============================================================================