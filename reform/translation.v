Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.

Require Sorts PTS PTS_Ext.
Module S := PTS_Ext.
Module T := PTS.
Import T Sorts.withoutProp.
