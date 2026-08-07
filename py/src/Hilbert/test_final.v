Require Hilbert.Hilbert.HilbertStructure.
Section Test.
  Variable I : Hilbert.Hilbert.HilbertStructure.IncidenceStructure.
  Variable O : Hilbert.Hilbert.HilbertStructure.OrderStructure I.
  Variable A B C : Hilbert.Hilbert.HilbertStructure.IncPoint I.
  Check Bet I O A B C.
  Check O.(Bet) A B C.
  Check Bet A B C.
End Test.
