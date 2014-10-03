
CONSTANTS 	DC,		\* Set of all DataCenters
 			Phar,	\* Set of all Pharmacies
 			Pat,	\* Set of all Patients
 			Tre,	\* Set of all Treatments
 			Pres	\* Set of all Prescriptions

VARIABLE patiendb, clock


Init == 
	/\ patientdb = [p \in P |-> treat |-> {}, 
								presc |-> {},
								taken |-> {} ]
	/\ clock = [d \in DC |-> 0 ]



\* Local Operation at the datacenter d that represents adding a treatment t to patient p by doctor doc 
\* Pre:		- doc, p, t all exist and belong to their set.
\* Post:	- The patient p treatment t is updated in the local DC d.
\*			- The logical clock is incremented by one.

addTreatment(d, doc, p, t) ==
	LET 
		date = clock[d] + 1
		s = patientdb[d]
		treatment = <<doc, p, date>>
		ns = [ treat |-> s[p].treat \/ treatment]
	IN
		patientdb' = [ patientdb EXCEPT ![d][p] = ns]
		clock' = [clock EXCEPT ![d] = date]



\* Local Operation at the datacenter d that represents adding a prescription pres to the treatment <<doc, t, date>>
\* Pre:		- doc, pres, t all exist and belong to their set.
\* Post:	- If the <<doc, t, date>> exists it adds a the prescription.

addPrescription(d, doc, t, clock, pres) 
	LET 
		date = clock[d]
		prescription = << doc, t, date>>
		s = patientdb[d]

		IF \E <<doc, t, date>> \in s[p].treat  \* A treatment has been issued.
		THEN

		ELSE
			\* Massible Cataclism or How do we solve this problem.

		ns = [ treat |-> s[d].treat, \* Use this to check is the same treatment, or that it exists
			   presc |-> prescription \/ s[d].pres,
			   taken |-> s[d].taken
			 ]
	IN
		patientdb' = [patientdb EXCEPT ![d][p] = ns]

\* Local Operation at the datacenter d that represents consuming a prescription pres in a pharmacy f by a patient p
\* Pre:		- f, p, pres all exists and belongs to their set.
\* Post: 	- 

giveDrug(d,f,p,pres)
	LET
		s = patientdb[d]
		ns = [ 	treat |-> s[d].treat,
				presc |-> s[d].presc,
				taken |-> << f, <<doc,t,clock>> >> \/ s[d].taken
			]
	IN
		patientdb' = [ patientdb EXCEPT ![d][p] = ns ]


Consistency == 
	
Next == <<patientdb>>

Spec == Init /\ [][Next]_vars