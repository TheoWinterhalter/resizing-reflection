This contains a translation heavily relying upon previous formalizations by Vincent Siles and Hugo Herbelin avialable here:
http://www.lix.polytechnique.fr/~vsiles/coq/PTSATR.html
http://www.lix.polytechnique.fr/coq/pylons/coq/pylons/contribs/view/PTSATR/trunk
as well as the modifications brought by Simon Boulier for the paper "The Next 700 Syntactical Models of Type Theory".

`Sort.v` contains the basic definitions related to sorts.  
`PTS.v` contains a formalization of MLTT + some axioms which will be the target of our translation.  
`PTS_Ext.v` contains a formalization of MLTT + reflection.
`translation.v` contains the translation from MLTT + reflection to
MLTT + axiom
