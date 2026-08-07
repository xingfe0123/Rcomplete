Require Hilbert.HilbertStructure.
Section Test.
  Variable I : IncidenceStructure.
  Variable O : OrderStructure I.
  Variable A B C : IncPoint I.
  Check Bet I O A B C.
  Check O.(Bet) A B C.
End Test.
