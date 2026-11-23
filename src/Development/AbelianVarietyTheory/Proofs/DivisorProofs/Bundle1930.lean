module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapAllTuplesCoeffFieldOfClauses
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.TwistField

open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem oneMapOverL_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hC : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀)) (hpb : T.pb = R.C.P.pb)
    (hO : OMPins T R κ v₀ O i) (hph : PhaseTie T R κ v₀ O ph i) (hio : IoExt R) (h0 : OneMapRow0 T R κ v₀ O i)
    (hex : PinsOverL T R κ v₀ i) (hsp : LiftsSpan R i (v₀ i (sg0 D A))) : OneMapOverL T R κ v₀ (ph i) i := by
  have hrow := hph h0
  obtain ⟨w⟩ := id hW
  have hT := w.laws
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hn : (κ i).n = (Vc D i).rank :=
    (w.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, hlam, hU⟩ := _root_.GlobalTheory.PtIdCore.point_identity_core D G Pl0 T0 A T R F κ v₀ hC h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hF₀, hP₀⟩ := hex
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := GlobalTheory.LiftSpanClauses.exists_retie_core O₀ hC
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hF₁ : O₁.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange := e₁ ▸ hF₀
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := hF₁.ge
  obtain ⟨c0, hr, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  have hid := hU _ _ (O i) hO.1.ge hP rfl hc c0 hx
  have hid₁ := hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁
  have hE₁ := GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ O₁ hle₁ hP₁
  have n0 := ne_zero_of_root hr
  have n1 := ne_zero_of_root hr₁
  by_cases hz : ∀ y, liftQ R i (v₀ i (sg0 D A)) A.μ0 y = 0
  · exact ⟨O₁, hF₁, hP₁, oneMapOf_of_ptIdent hT hV hn hP hrow hle₁ hP₁ hlev₁ hE₁ hsp hlam n0 n1 hid hid₁ (Or.inr hz)⟩
  · obtain ⟨y, hy⟩ := not_forall.1 hz
    have hu := const_ratio_mem hT hV hn hO.1 hP hrow hle₁ hP₁ hlev₁ hE₁ hlam n1 hid hid₁ hy
    have e : ((⟨c0 / c1, hu⟩ : O₁.c'.F) : ℂ) * c1 = c0 := div_mul_cancel₀ _ n1
    have hx₂ := xiConst_scaleXi O₁ ⟨c0 / c1, hu⟩ hx₁
    have hP₂ := pins_scaleXi O₁ ⟨c0 / c1, hu⟩ (fun h => div_ne_zero n0 n1 (congrArg Subtype.val h)) hx₁ (e.symm ▸ hr) hP₁
    rw [e] at hx₂
    exact ⟨scaleXi O₁ ⟨c0 / c1, hu⟩, hF₁, hP₂, oneMapOf_of_ptIdent (O' := scaleXi O₁ ⟨c0 / c1, hu⟩) hT hV hn hP hrow hle₁ hP₂ hlev₁
      (GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂) hsp hlam n0 n0 hid
      (hU _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂ hlev₁ hc₁ c0 hx₂) (Or.inl rfl)⟩

end GlobalTheory.TwistField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.DimAtOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_dimAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := by
  intro D i τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt
  have h := Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ (GlobalTheory.AdelicScalar.sig_add i τ)
  have h1 : (1 : ℚ) ≤ dimK _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) τ) :=
    one_le_mul_of_one_le_of_one_le (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.1) (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.2.1)
  exact_mod_cast h1

end GlobalTheory.DimAtOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PosThrough

theorem one_le_interNumRed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → ∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed k Z (fun _ : Fin e => N) := by
  intro hNN k _ X q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x hNef ha hcls hamp hN₂ Z e hZ hx he hdim
  have hBig : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q →
      letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X),
      IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N :=
    GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN
  have hAmp : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
      AmpleAt N (π x) → AmpleAt (N.pull π) x := _root_.GlobalTheory.AmplePull.ampleAt_pull
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ
  set q' := redι Z ≫ q with hq'
  letI := algebraΓOfHom q'
  have hi : ∀ r : k, (redι Z).appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r :=
    fun r => rfl
  have hpq : IsProjOver q' := by
    obtain ⟨n, f, hf, hs⟩ := hq
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs]⟩
  obtain ⟨w, rfl⟩ : x ∈ Set.range (redι Z) := by rw [range_redι]; exact hx
  have hb := hBig k _ q' hpq (N.pull (redι Z)) (N₁.pull (redι Z)) (N₂.pull (redι Z))
    (LB.isLB_pull hN _) (LB.isLB_pull h₁ _) (LB.isLB_pull h₂ _) a w
    (hNef.pull_of_isClosedImmersion _ hi) ha
    (by rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add (f := _)])
    (hAmp _ _ _ N₁ h₁ w hamp) (hN₂.pull_of_isClosedImmersion _ hi)
  have hstr : strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = q' :=
    strHom_eq (f := q') fun _ => rfl
  have hD : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = e :=
    (topologicalKrullDim_red Z).trans hdim
  have hpos := ((hNN.2.2.isBig_iff (hstr ▸ hpq) hD (hNef.pull_of_isClosedImmersion _ hi)).1 hb)
  have heq : interNumRed k Z (fun _ : Fin e => N) = topSelfIntersection k (N.pull (redι Z)) e :=
    interNumOn_const_eq_topSelf hi hN e
  omega

end GlobalTheory.PosThrough
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowAllTuplesOfCoreClauses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hR hoff hused hfw hio i hpins htie hspan
  have hin : TieIn T R κ v₀ := _root_.GlobalTheory.tieIn_of_nonempty_tie D G Pl0 T0 A T R κ v₀ hfw
  refine GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span D G Pl0 T0 A T R κ v₀ O ph i hR.lev hR.grp.chiW hR.fam hR.models hpins htie
    (_root_.GlobalTheory.OneMapTies.oneMapRow0_of_ties_core hCI D G Pl0 T0 A T R F κ v₀ hR hin hio O i hpins) (fun hG => ?_)
    (_root_.GlobalTheory.OneMapAll.identityRow_of_core hCI D G Pl0 T0 A T R F κ v₀ hR hin hio i) hspan
  obtain ⟨O', h1, h2, -⟩ := _root_.GlobalTheory.PinnedTuples.exists_pins_of_base D G Pl0 T0 A T R κ v₀ O hR.lev hR.grp.chiW hR.fam hR.models hR.thP.vP hoff hused
    hfw i hpins hG
  exact ⟨O', h1, h2⟩

end GlobalTheory.OneMapCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
section
noncomputable section

namespace GlobalTheory.CovTop.VolUp

open NumberField MeasureTheory Matrix Formalism.BasicNotions GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

def dg {ι : Type} [DecidableEq ι] (a₀ : ι) (z : ℂ) : Matrix ι ι ℂ := Matrix.diagonal (Function.update 1 a₀ z)

def sMat {p q : ℕ} (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  UpqT.mat u * dg a₀ (UpqT.mat u).det⁻¹

def permM {ι : Type} {r : ℕ} (e : ι ≃ Fin r) : Matrix ι (Fin r) ℂ := Matrix.of fun i j => if e i = j then 1 else 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def frBall (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (ε : ℝ) : Set (realSU Ψ G) :=
  {s | ∀ τ a b, ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε}

def IsIdent {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) : Prop :=
  ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ = -(G.map (σ ρ).1)ᵀ ∧ A ρ * mat x (σ ρ) = permM (e ρ)

def IsProj {κ : Type} (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ))
    (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) : Prop :=
  ∀ b ρ, A ρ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = sMat (a₀ ρ) (b ρ) * A ρ

section Adelic

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsRealPart {D : D7} (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V → ∀ ρ, Upq V ρ) : Prop :=
  ∀ h ρ, UpqT.mat (rp h ρ) * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h

end Adelic

theorem permM_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) : permM e * (permM e)ᵀ = 1 := by
  ext i j
  simp [permM, Matrix.mul_apply, Matrix.one_apply, eq_comm]

theorem transpose_mul_permM {ι : Type} [Fintype ι] (e : ι ≃ Fin r) : (permM e)ᵀ * permM e = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← e.symm.sum_comp]
  simp [permM, Matrix.one_apply, eq_comm]

theorem det_dg {ι : Type} [Fintype ι] [DecidableEq ι] (a₀ : ι) (z : ℂ) : (dg a₀ z).det = z := by
  rw [dg, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

end GlobalTheory.CovTop.VolUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatible
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftW

theorem one_left_eq {T : Scheme.{0}} {X : Over T} {M : Over T} [GrpObj M] :
    (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem one_left_comp_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have hxx : x₀ * x₀ = x₀ := by
    ext
    exact e
  have h1 : x₀ = 1 := mul_eq_right.mp hxx
  exact congrArg Over.Hom.left h1

end GlobalTheory.FlatModel.LiftW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionFirstPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow.TrSec

variable {S : Scheme.{0}} (P : PolAV S)

lemma chart_le (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)).U j ≤ (snd (baseOver S) P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L _ j 0

def thSec (s : P.L.Sec) : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)) where
  f j := ReciprocityTheory.ChartRestriction.G.DVR.rs (chart_le P j) (((snd (baseOver S) P.A).left.app (P.L.U (j 0))).hom (s.f (j 0)))
  compat i j := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic (snd (baseOver S) P.A).left (chart_le P i) (chart_le P j)
      (s.f (i 0)) (s.f (j 0)) (P.L.g (i 0) (j 0)) (s.compat _ _) _ ?_
    simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
    rfl

lemma projectionPullbackSectionBaseProduct_isInverseImage (s : P.L.Sec) : IsPolAVSectionInverseImage P (baseOver S) s (thSec P s) := by
  intro i h
  rfl

lemma snd_inv (p : P.A.left) : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := by
  have e : (λ_ P.A).inv ≫ snd (baseOver S) P.A = 𝟙 P.A := (λ_ P.A).inv_hom_id
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
  rfl

lemma nonzero_thSec (s : P.L.Sec) (p : P.A.left) (hp : p ∈ nonzeroLocus s) :
    (λ_ P.A).inv.left.base p ∈ nonzeroLocus (thSec P s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, ?_⟩
  have hq : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := snd_inv P p
  show _ ∈ (baseOver S ⊗ P.A).left.basicOpen
    (((baseOver S ⊗ P.A).left.presheaf.map (homOfLE (chart_le P (fun _ => k))).op).hom
      (((snd (baseOver S) P.A).left.app (P.L.U k)).hom (s.f k)))
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
  refine ⟨?_, ?_⟩
  · show _ ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ (P.L.U k : Set P.A.left)
    rw [hq]; exact P.A.left.basicOpen_le _ hk
  · show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ P.A.left.basicOpen (s.f k)
    rw [hq]; exact hk

end GlobalTheory.MBLow.TrSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesReparamBoundedCoefficients
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem regroup_fib_tsum {X M : Type} [AddCommMonoid M] [TopologicalSpace M] (n : X → ℕ) (i : ℕ)
    (h : {α | n α = i}.Finite) (f : X → M) :
    ∑' b : n ⁻¹' {i}, f b = ∑ α ∈ h.toFinset, f α := by
  have hs : n ⁻¹' {i} = (h.toFinset : Set X) := by ext; simp
  rw [← Finset.tsum_subtype', ← hs]

theorem lattice_series_regroup : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) (n : X → ℕ) (π : C) (a : X → C) (b : ℝ), π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ α, ‖a α‖ ≤ b * ‖π‖ ^ n α) → ∃ Θ : PowerSeries C, (∀ i, ‖PowerSeries.coeff i Θ‖ ≤ max b 0) ∧ ∑' i, PowerSeries.coeff i Θ * π ^ i = ∑' α, a α ∧ ∀ (e : C →+* ℂ) (u : ℂ), (Summable fun α => ‖e (a α) * (u / e π) ^ n α‖) → (Summable fun i => ‖e (PowerSeries.coeff i Θ) * u ^ i‖) ∧ ∑' i, e (PowerSeries.coeff i Θ) * u ^ i = ∑' α, e (a α) * (u / e π) ^ n α := by
  intro C _ _ _ X n π a b hπ0 hπ1 hfin hb
  classical
  have hmem : ∀ i α, α ∈ (hfin i).toFinset ↔ n α = i := fun i α => by simp
  have hn : Filter.Tendsto n Filter.cofinite Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun N => Filter.eventually_cofinite.2 ?_
    refine ((Set.finite_lt_nat N).biUnion fun i _ => hfin i).subset ?_
    intro α hα
    simp only [Set.mem_setOf_eq, not_le] at hα
    exact Set.mem_biUnion (x := n α) hα rfl
  have hpow : Filter.Tendsto (fun α => b * ‖π‖ ^ n α) Filter.cofinite (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1).comp hn).const_mul b
  have ha0 : Filter.Tendsto a Filter.cofinite (nhds 0) := squeeze_zero_norm hb hpow
  have ha : Summable a := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha0
  refine ⟨PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i, ?_, ?_, ?_⟩
  · intro i
    rw [PowerSeries.coeff_mk]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun α hα => ?_
    have hpi : 0 < ‖π‖ ^ i := pow_pos (norm_pos_iff.2 hπ0) _
    rw [norm_div, norm_pow, div_le_iff₀ hpi]
    have := hb α
    rw [(hmem i α).1 hα] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpi.le)
  · rw [← ((ha.hasSum.tsum_fiberwise n).tsum_eq)]
    refine tsum_congr fun i => ?_
    rw [PowerSeries.coeff_mk, regroup_fib_tsum n i (hfin i), Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => div_mul_cancel₀ _ (pow_ne_zero _ hπ0)
  · intro e u hsum
    have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
    have hkey : ∀ i, e (PowerSeries.coeff i (PowerSeries.mk fun i => ∑ α ∈ (hfin i).toFinset, a α / π ^ i)) * u ^ i
        = ∑ α ∈ (hfin i).toFinset, e (a α) * (u / e π) ^ n α := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [PowerSeries.coeff_mk, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [(hmem i α).1 hα, map_div₀, map_pow, div_pow]
      field_simp
    simp_rw [hkey]
    have hf : Summable fun α => e (a α) * (u / e π) ^ n α := hsum.of_norm
    refine ⟨?_, ?_⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => norm_sum_le _ _) ?_
      have := (hsum.hasSum.tsum_fiberwise n).summable
      exact this.congr fun i => regroup_fib_tsum n i (hfin i) (fun α => ‖e (a α) * (u / e π) ^ n α‖)
    · rw [← ((hf.hasSum.tsum_fiberwise n).tsum_eq)]
      exact tsum_congr fun i => (regroup_fib_tsum n i (hfin i) _).symm

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropertyOfCodimOneLocalUnits
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HartogsUnit

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def toFrac (p : Ideal A) [p.IsPrime] : Localization.AtPrime p →+* FractionRing A :=
  IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
    (g := algebraMap A (FractionRing A))
    (fun s => IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors s.2)))

theorem toFrac_comp (p : Ideal A) [p.IsPrime] :
    (toFrac p).comp (algebraMap A (Localization.AtPrime p)) = algebraMap A (FractionRing A) :=
  IsLocalization.lift_comp _

theorem toFrac_mem (p : Ideal A) [p.IsPrime] (w : Localization.AtPrime p) :
    ∃ s, s ∉ p ∧ s • toFrac p w ∈ (algebraMap A (FractionRing A)).range := by
  obtain ⟨⟨m, s⟩, e⟩ := IsLocalization.surj p.primeCompl w
  refine ⟨s, s.2, m, ?_⟩
  have h := congrArg (toFrac p) e
  simp only [map_mul] at h
  rw [← RingHom.comp_apply (toFrac p), ← RingHom.comp_apply (toFrac p), toFrac_comp] at h
  rw [Algebra.smul_def, mul_comm, h]

end GlobalTheory.HartogsUnit
end

