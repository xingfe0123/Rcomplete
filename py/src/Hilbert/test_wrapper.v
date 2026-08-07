Require Hilbert.HilbertStructure.
Set Implicit Arguments.
Section Test.
  Variable I : IncidenceStructure.
  Variable O : OrderStructure I.
  Variable Cstr : CongruenceStructure I O.
  Variable A B C D E F : IncPoint I.
  Check Bet_ A B C.
  Check CongSeg_ A B C D.
  Check CongAng_ A B C D E F.
End Test.
