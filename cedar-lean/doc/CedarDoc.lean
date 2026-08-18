import VersoManual
import CedarDoc.Decimal
import CedarDoc.Datetime
import CedarDoc.Duration
import CedarDoc.IPAddr

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Verified Cedar Extension Parsers in Lean 4" =>

%%%
authors := ["Cruise Song (Amazon Web Services)"]
%%%

This document specifies Cedar's extension parsers and proves their correctness properties. All theorems are machine-checked in Lean 4.

{include 1 CedarDoc.Decimal}

{include 1 CedarDoc.Duration}

{include 1 CedarDoc.Datetime}

{include 1 CedarDoc.IPAddr}
