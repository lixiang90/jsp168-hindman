module
public import Init

namespace AuditPrivateProbe

-- Deliberately unapproved axioms in an isolated ignored test fixture.
-- Neither this module nor its audit is part of the proof source closure.
private axiom hiddenUnusedAxiom : True
private theorem hiddenUnusedProof : True := hiddenUnusedAxiom

private axiom hiddenUsedAxiom : True
public theorem exportedUsingPrivate : True := hiddenUsedAxiom
public theorem exportedClean : True := True.intro

end AuditPrivateProbe
