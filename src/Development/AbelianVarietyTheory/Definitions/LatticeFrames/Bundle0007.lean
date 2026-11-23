module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
section
noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Deg

def CollS {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : Prop :=
  (Y.tO u u).pairAbs ((Y.tO u u).big (Y.tO u u).nzSet) ≤
    (Real.sqrt ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)))⁻¹ ^ (D.R.k * D.R.f) * ddC X Y u u +
      Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k) / 2) * duC X Y u

end GlobalTheory.Core.Deg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
section
noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.MiS
open _root_.Formalism Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FreeSingleHomotopyEquivDiscreteChains

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end FreeSingleHomotopyEquivDiscreteChains

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def OpsUnit (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  (∀ e ∈ X.EEl true, V e ∈ X.EEl true ∧ ‖V e‖ = ‖e‖) ∧
    ∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x

variable {X cr cv}

end Gen

end GlobalTheory.MiS

end
end

