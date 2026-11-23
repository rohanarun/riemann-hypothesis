module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfLePolyExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOrthogonality
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFibreSimplyTransitive
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfRationalExpansions
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem isRatPath_of_isRat : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y),
    (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  intro F _ Y ξ hrat
  obtain ⟨h1, -, -, h4, h5, h6, -⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  obtain ⟨U, hUa, hy, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show ξ (IsLocalRing.closedPoint (PowerSeries F)) ∈ (⊤ : Y.Opens) from trivial)
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := (h4 _ Y ξ U).2 hy
  set ψ := evAt ξ hξ
  set ιR := algebraMap (RatFunc F) (LaurentSeries F)
  set ιP := algebraMap (PowerSeries F) (LaurentSeries F)
  have hR : Function.Injective ιR := ιR.injective
  have hmem : ∀ f, (ιP.comp ψ) f ∈ ιR.range := fun f => by
    obtain ⟨ρ, hρ⟩ := (isRat_iff_exists_ratFunc F (ψ f)).1 (hrat U hUa hξ f)
    exact ⟨ρ, hρ⟩
  let e := RingEquiv.ofBijective ιR.rangeRestrict ⟨fun a b hab => hR (congrArg Subtype.val hab), ιR.rangeRestrict_surjective⟩
  let φ : Γ(Y, U) →+* RatFunc F := e.symm.toRingHom.comp ((ιP.comp ψ).codRestrict ιR.range hmem)
  have hφ : ∀ f, ιR (φ f) = ιP (ψ f) := fun f => by
    have := congrArg Subtype.val (e.apply_symm_apply ((ιP.comp ψ).codRestrict ιR.range hmem f))
    exact this
  obtain ⟨β, hβ, hβφ⟩ := h6 (RatFunc F) Y U hUa φ
  refine ⟨β, ?_⟩
  have ha : ⊤ ≤ (spMap ιR ≫ β) ⁻¹ᵁ U := fun x _ => hβ (Set.mem_univ ((spMap ιR) x))
  have hb : ⊤ ≤ (spMap ιP ≫ ξ) ⁻¹ᵁ U := fun x _ => hξ (Set.mem_univ ((spMap ιP) x))
  refine h5 (LaurentSeries F) Y _ _ U hUa ha hb ?_
  refine RingHom.ext fun f => ?_
  rw [h1 _ _ Y ιR β U hβ ha f, h1 _ _ Y ιP ξ U hξ hb f, hβφ]
  exact hφ f

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOfMulEqSmul
section
noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct

namespace GlobalTheory.SelfDualFil

theorem isRegular_of_mul_eq_smul {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) : IsRegular M ∧ IsRegular N := by
  have hd : M.det * N.det ≠ 0 := by
    rw [← Matrix.det_mul, H, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact ⟨Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (left_ne_zero_of_mul hd)).1,
    Matrix.isRegular_of_isLeftRegular_det (IsRegular.of_ne_zero (right_ne_zero_of_mul hd)).1⟩

theorem mul_eq_smul_comm {A : Type} [CommRing A] [IsDomain A] {h : ℕ}
    {M N : Matrix (Fin h) (Fin h) A} {c : A} (hc : c ≠ 0)
    (H : M * N = c • (1 : Matrix (Fin h) (Fin h) A)) :
    N * M = c • (1 : Matrix (Fin h) (Fin h) A) := by
  apply (isRegular_of_mul_eq_smul hc H).1.1
  show M * (N * M) = M * (c • 1)
  rw [← Matrix.mul_assoc, H]
  simp

section

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h : ℕ} {Γ : Type} [CommRing Γ]
  [Algebra ℤ_[p] Γ]

theorem G_eq [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    D.G = D.G.map (phiInv p O) * D.Ψ' := by
  apply (isRegular_of_mul_eq_smul hμ D.G_mul_F).2.2
  show D.G * D.F = D.G.map (phiInv p O) * D.Ψ' * D.F
  have e1 : D.G.map (phiInv p O) * D.F.map (phiInv p O) = nu ε • 1 := by
    rw [← Matrix.map_mul, D.G_mul_F]
    ext1 i j
    by_cases hij : i = j <;> simp [hij, phiInv_mu]
  have e2 : D.Ψ' * D.F = xi ε • D.F.map (phiInv p O) := by
    conv_lhs => rw [D.F_eq]
    rw [← Matrix.mul_assoc, mul_eq_smul_comm hξ D.Ψ_mul]
    simp
  rw [Matrix.mul_assoc, e2, Matrix.mul_smul, e1, smul_smul, xi_mul_nu, D.G_mul_F]

def dualDatum [IsDomain (Ainf p O)] (hμ : mu ε ≠ 0) (hξ : xi ε ≠ 0) (D : Datum ε h Γ) :
    Datum ε h ℤ_[p] where
  F := D.Gᵀ
  G := D.Fᵀ
  Ψ := D.Ψ'ᵀ
  Ψ' := D.Ψᵀ
  ρT := (etale ε h).ρT
  ρM := (etale ε h).ρM
  G_mul_F := by rw [← Matrix.transpose_mul, D.G_mul_F]; simp
  F_eq := by
    rw [Matrix.transpose_map, ← Matrix.transpose_mul, ← G_eq hμ hξ D]
  Ψ_mul := by rw [← Matrix.transpose_mul, D.Ψ_mul]; simp
  F_act := by
    intro a
    have e : ((etale ε h).ρT a).map (ofPadic p O) = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, hij]
    have e' : (etale ε h).ρM a = ofPadic p O a • 1 := by
      ext1 i j
      by_cases hij : i = j <;> simp [etale, Matrix.algebraMap_matrix_apply, hij]
    rw [e, e']
    simp

variable (C : Type) [Field C] [Algebra O C]

end

end GlobalTheory.SelfDualFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapOrbUnitEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrbCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cp_conj {n : ℕ} {w : Pl E} (g γ : UL n w) :
    (g⁻¹ * γ * g).1.val.charpoly = γ.1.val.charpoly := by
  have h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h
  rw [h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val

theorem mk_eq_iff {G : Type} [Group G] (x y : G) :
    (Quot.mk _ x : TwCl (MonoidHom.id G)) = Quot.mk _ y ↔ ∃ g : G, y = g⁻¹ * x * g := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩
    | refl a => exact ⟨1, by simp⟩
    | symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g, hg⟩ := ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩
  · rintro ⟨g, hg⟩
    exact Quot.sound ⟨g, by simpa using hg⟩

theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  refine ⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩
  haveI : Nonempty (Pl E) := ⟨w⟩
  have hspec := Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩
  refine ⟨_, ⟨?_, hspec⟩, ?_⟩
  · show _ = _
    simp only [hspec]
  · rintro u ⟨hu, hu'⟩
    rw [Set.mem_setOf_eq] at hu
    rw [hu]
    simp only [hu']

theorem ell_mul {n : ℕ} (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree) (h2 : p₂ ∈ Ell E p₂.natDegree)
    (hc : IsCoprime p₁ p₂) (hn : p₁.natDegree + p₂.natDegree = n) : p₁ * p₂ ∈ Ell E n := by
  obtain ⟨m1, -, s1, r1⟩ := h1
  obtain ⟨m2, -, s2, r2⟩ := h2
  refine ⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, Polynomial.roots_mul] at hz
  · rcases Multiset.mem_add.1 hz with h | h
    · exact r1 τ z h
    · exact r2 τ z h
  · rw [← Polynomial.map_mul]
    exact ((m1.mul m2).map τ).ne_zero

end GlobalTheory.UnitOrbCount

namespace GlobalTheory.UnitOrbCount

end GlobalTheory.UnitOrbCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.La1sqEqOfUnXEq
section
noncomputable section

namespace GlobalTheory.CuspUnif

section Decay

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_decay (X : Data E r) (hr : 0 < r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {C c : ℝ} (hc : 0 < c) (h : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-c / X.firstMinimumSq x)) : P ∈ X.SS la := by
  have := GlobalTheory.ModeDecay.nonempty_cmType X
  set f : ℝ := (Fintype.card X.Ψ : ℝ) with hf
  have hf0 : 0 < f := Nat.cast_pos.2 Fintype.card_pos
  have hπ := Real.pi_pos
  refine ⟨hP, fun ξ hξ x hx => GlobalTheory.ModeDecay.fj_eq_zero_of_decay GlobalTheory.fj_norm_mul_exp_le_sup_flow
    ReciprocityTheory.ChartRestriction.G.AR.Inst.la1GGStatement_firstMinimum r X la P (c / (8 * Real.pi * f)) hP.1
    ⟨Real.sqrt |C|, 0, le_rfl, fun y hy η hη h2 => ?_⟩ ξ hξ 0 (by simpa using by positivity) x hx⟩
  set t := ⨅ τ, X.tt η y τ with ht
  have ht2 : 2 ≤ t := le_ciInf h2
  have ht' : 0 < t := by linarith
  have hpos : ∀ v : Fin r → E, v ≠ 0 → ∀ τ, 0 < X.c τ * X.maj y τ (Data.emb τ.1 v) := fun v hv τ =>
    mul_pos (TwoSidedBoostBounds.c_pos X τ) (X.maj_pos hy τ (emb_ne_zero τ.1 hv))
  have hle : ∀ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) ≤ 1 / t := fun τ =>
    (le_one_div ht' (hpos η hη.2.2 τ)).1 (ciInf_le (f := fun τ => X.tt η y τ) (Finite.bddBelow_range _) τ)
  have hla : X.firstMinimumSq y ≤ f / t :=
    calc X.firstMinimumSq y ≤ ∑ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) := by
          refine csInf_le ⟨0, ?_⟩ ⟨η, hη.1, hη.2.2, rfl⟩
          rintro _ ⟨v, -, hv, rfl⟩
          exact Finset.sum_nonneg fun τ _ => (hpos v hv τ).le
      _ ≤ ∑ _τ : X.Ψ, 1 / t := Finset.sum_le_sum fun τ _ => hle τ
      _ = f / t := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  have hla0 : 0 < X.firstMinimumSq y := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom X hr hy)
  have hexp : Real.exp (-c / X.firstMinimumSq y) ≤ Real.exp (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have : c / (f / t) ≤ c / X.firstMinimumSq y := div_le_div_of_nonneg_left hc.le hla0 hla
    have e1 : ((2 : ℕ) : ℝ) * (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) = -(c / (f / t)) := by
      push_cast
      field_simp
      norm_num
    rw [e1, neg_div]
    linarith
  rw [Real.rpow_zero, mul_one]
  refine (Real.le_sqrt_of_sq_le ((h y hy).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left hexp (abs_nonneg C))))).trans_eq ?_
  rw [Real.sqrt_mul (abs_nonneg C), Real.sqrt_sq (Real.exp_pos _).le]

end Decay

section Unif

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric GlobalTheory.SupFull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Unif

end GlobalTheory.CuspUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionFramedPointsIsActionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_framedPoints_isAction : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) , R.toLevCh.Is A.μ0 → LawsJ T → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La), LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) c' (fun g => (lev g, (LinearMap.id : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))) := by
  first | exact @GlobalTheory.LevelActFromLevel.actLev_of_levIs | exact GlobalTheory.LevelActFromLevel.actLev_of_levIs | (intros; apply GlobalTheory.LevelActFromLevel.actLev_of_levIs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChanges
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevOrbit

def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Submodule R M) (f g : M →ₗ[R] M)
    (hK : ∀ a ∈ K, f a ∈ K) (hK' : ∀ a ∈ K, g a ∈ K) (hfg : ∀ a, f (g a) - a ∈ K) (hgf : ∀ a, g (f a) - a ∈ K) :
    (M ⧸ K) ≃ₗ[R] (M ⧸ K) :=
  LinearEquiv.ofLinear (K.mapQ K f (fun a ha => hK a ha)) (K.mapQ K g (fun a ha => hK' a ha))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hfg a))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hgf a))

theorem smul_top_comap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    ∀ a ∈ (I • ⊤ : Submodule R M), f a ∈ (I • ⊤ : Submodule R M) := by
  have h : (I • ⊤ : Submodule R M) ≤ (I • ⊤ : Submodule R M).comap f := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact fun a ha => h ha

theorem exists_gam_of_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (g : Sim Dw) :
    ∃ γ : Gam Dw l₂, ∀ a, γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f l₂.M a) := by
  obtain ⟨h, hh⟩ := g.inv l₂.M (GlobalTheory.LevelFibre.level_pos l₂)
  exact ⟨quotEquiv _ (g.f l₂.M) h (smul_top_comap _ _) (smul_top_comap _ _)
    (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).2) (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).1),
    fun a => rfl⟩

theorem fibre_torsor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → (FrOver d y₂' y ↔ ∃ γ, CongMod l.Mb (lift γ) LinearMap.id ∧ levR (lift γ, LinearMap.id) y₂ y₂') ∧ ∀ γ γ', levR (lift γ, LinearMap.id) y₂ y₂' → levR (lift γ', LinearMap.id) y₂ y₂' → γ = γ' := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hA hbase lift hlift k _ _ _ _ hk y₂ y₂' y hy
  obtain ⟨hd, hM, -, -, -, hE, -, -, -⟩ := id hlev
  have hLaws : ReciprocityTheory.ChartRestriction.G.Out.Laws := _root_.GlobalTheory.abelianSchemeLaws_all.1
  have hN := GlobalTheory.levelMaps_closed hLaws E H Dw hpq
  refine ⟨⟨fun h' => ?_, fun ⟨γ, hγ, hr⟩ => ?_⟩, fun γ γ' h₁ h₂ => GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique E H Dw d.l₂ d.Xo₂ d.c₂ hpq hA lift hlift k y₂ y₂' γ γ' h₁ h₂⟩
  · obtain ⟨g, ρ, ν, hg, -, hmv, hfr⟩ :=
      GlobalTheory.exists_levMove_of_frOver hLaws E H Dw l Xo c 0 d hN hd hM hE d.r d.m hE k hk y y₂ y₂' hy h'
    obtain ⟨γ, hγ⟩ := exists_gam_of_sim d.l₂ g
    have hl : ∀ a, lift γ a - g.f d.l₂.M a ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
      have e := congrArg (fun f => f a) (hlift γ)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, hγ] at e
      exact (Submodule.Quotient.eq _).1 e
    refine ⟨γ, fun a => ?_, (GlobalTheory.LevelActionOfLifts.levR_congr hl y₂ y₂').2 ⟨ρ.hom, ν, inferInstance,
      ⟨hmv.1, hmv.2.1, fun a => ?_⟩, hfr⟩⟩
    · have h1 : lift γ a - g.f d.l₂.M a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
        Submodule.smul_mono_left hd.2.1 (hl a)
      have h2 := GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg a
      have := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at this
    · have e : ∀ x x', d.Xo₂.univ.etaA x = d.Xo₂.univ.etaA x' := fun x x' => by
        have h1 := d.Xo₂.univ.etaA_ker x
        have h2 := d.Xo₂.univ.etaA_ker x'
        rw [hA, one_smul] at h1 h2
        rw [h1, h2]
      rw [e (LinearMap.id a) (g.f d.l₂.A a)]
      exact hmv.2.2 a
  · obtain ⟨ρ₂, ν₂, hi, hmv, hfr⟩ := hr
    obtain ⟨e₁, e₂⟩ := _root_.GlobalTheory.levMove_comm_levelMap_of_trivial_mod E H Dw l Xo c 0 d hpq hlev hA hbase ρ₂ ν₂ (lift γ) LinearMap.id hi hmv hγ
    obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
    exact GlobalTheory.frOver_of_square_of_frMove E H Dw l Xo c 0 d (𝟙 _) ι ρ₂ ν₂ d.r d.m (by rw [e₁, Category.comp_id])
      (by rw [e₂, hι, Category.comp_id]) k y y y₂ y₂' hy (hone k y) hfr

end GlobalTheory.LevOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqPrincipalRowsOfType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRowsPrincipal

theorem pLevE_of : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PLevE F := by
  intro hCusp hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hEx hJunk hGE hPos hScal hB hRT
  have hBlock : (R.toCx3 F).zs.InBlock := _root_.GlobalTheory.Hk3.inBlock_of_cuspRapidDecay hCusp R F hLI hOk hC hEx hGE
  have hCarry : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c := _root_.GlobalTheory.Hk3.carries_of_rows_top hCusp hHowe R F hLI hOk hC hEx hJunk hGE hPos
  have hSpan : (⨆ p, R.EEp3 p) = ⊤ :=
    _root_.GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top R F hC hEx (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) hCarry
  have hTop := GlobalTheory.T.EEg3_eq_univ_of_weakCharacterisation R F hOk hC hSpan hScal hB hRT hBlock
  obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  refine ⟨?_, ?_⟩
  · show (R.toCx3 F).EEl false = _ ⊓ _
    rw [hTop, top_inf_eq, h0]
  · show (R.toCx3 F).EEl true = _ ⊓ _
    rw [hTop, top_inf_eq, h1]

end GlobalTheory.LevelRowsPrincipal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowH1VanishesGeometricFibreAllStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundlePow_h1Vanishes_geometricFibre_all : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → RelAmple B M → ∀ a : ℕ, 1 ≤ a → GlobalTheory.AbLaw.FirstCohomologyVanishes (GlobalTheory.AbLaw.pw M (a : ℤ))) → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → ∀ a : ℕ, 1 ≤ a → ∀ (T : Over S) (K : Type) [Field K] [IsAlgClosed K] (q : Spec (CommRingCat.of K) ⟶ T.left), ∃ (X' : Scheme.{0}) (π : X' ⟶ (T ⊗ A).left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' (fst T A).left q ∧ GlobalTheory.AbLaw.FirstCohomologyVanishes ((LPow A L (a : ℤ) T).pull π) := by
  first | exact @GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | exact GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all | (intros; apply GlobalTheory.AbLaw.SecBC.exists_h1Zero_of_abVar_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

def IsCO (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))

end GlobalTheory.FunObj
end
end

