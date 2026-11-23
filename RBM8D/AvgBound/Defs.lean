module

public import RBM8D.LocalLaw.Defs
public import RBM8D.LocalLaw.Eta1
public import RBM8D.LocalLaw.Primed
public import RBM8D.GlobalExp.Strategy
public import RBM8D.GlobalExp.GlobalGoodRows
public import Batteries.Tactic.OpenPrivate
public import RBM8D.GlobalExp.SubstSPD
public import RBM8D.TExp.Second
import all RBM8D.GlobalExp.GlobalGoodRows
import all RBM8D.GlobalExp.SubstSPD
import all RBM8D.TExp.Second

@[expose] public section

/-!
# The averaged bound [II, Lemma 9.1] = [I, Lemma 5.6]: ghost edges

The data record with ghost factor `1`, used for the graphs with ghost edges of [II, Def 9.4]
(`Data.ghostOne`).
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory Filter Complex

namespace RBM8D.Graphs

variable {V E : Type}

/-! ## Ghost edges ([II, Def 9.4]) -/

/-- The data record with ghost factor `1`. A ghost edge is the factor `W²/L²`, and
[II, Def 9.4] multiplies the graph by `L²/W²` for each ghost edge, so the product has the value
of the graph at ghost factor `1`. -/
def Data.ghostOne {ι : Type*} (D : Data ι) : Data ι := { D with ghost := 1 }

end RBM8D.Graphs

namespace RBM8D

open Graphs

end RBM8D

namespace RBM8D.Graphs

end RBM8D.Graphs

namespace RBM8D

open Graphs

end RBM8D

namespace RBM8D.Graphs

end RBM8D.Graphs

namespace RBM8D

open Graphs

end RBM8D

namespace RBM8D.Graphs

-- (the names formerly opened from RBM8D.GlobalExp.GlobalGoodRows are public)
open private SubstSPD_mgext from RBM8D.GlobalExp.SubstSPD
open private h2Rec_shape h2Rec_struct from RBM8D.TExp.Second

set_option synthInstance.maxSize 4000
set_option maxRecDepth 100000

end RBM8D.Graphs

namespace RBM8D

open Graphs

open private h2Rec_struct from RBM8D.TExp.Second

end RBM8D
