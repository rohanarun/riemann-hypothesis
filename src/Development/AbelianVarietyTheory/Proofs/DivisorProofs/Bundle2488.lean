module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmpleAlongPullbackTransportIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem gs_abCst {R : Type} [CommRing R] {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens)
    (r : Z ⟶ X) (z : Z) (hz : r z ∈ W) (x : R) :
    gs r z W (GlobalTheory.AbLaw.cst f W x) = gs (r ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) :=
  (gs_res r z le_top hz _).trans (gs_pull r f z ⊤ trivial _)

theorem gs_top_mul {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a * b)) =
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) *
        gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b) := by
  rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem isUnit_gs_top {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (a : Rˣ) :
    IsUnit (gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a : R))) := by
  rw [gs_eq q z ⊤ trivial]
  exact ((a.isUnit.map _).map _).map _

theorem veryAmpleAlong_transport {K : Type} [Field K] {X Y XA : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K))
    (pA : XA ⟶ Spec (CommRingCat.of K)) (gn : Y ⟶ XA) [IsIso gn] (hp : gn ≫ pA = p) (π : Y ⟶ X) {L : LB X}
    (hL : L.IsLB) {LA : LB XA} (hLA : LA.IsLB) {k m : ℕ} (b : Fin (m + 1) → H0 LA k)
    (hb : VeryAmpleAlong pA (𝟙 XA) LA b) (σ : Fin (m + 1) → H0 L k) (c : Fin (m + 1) → Kˣ)
    (H : ∀ (y : Y) (j : Fin 1 → L.ι) (jA : Fin 1 → LA.ι), π y ∈ L.U (j 0) → gn y ∈ LA.U (jA 0) →
      ∃ u : (Y.presheaf.stalk y)ˣ, ∀ i, secGerm π y (σ i) j =
        u.val * gs p y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) * secGerm gn y (b i) jA) :
    VeryAmpleAlong p π L σ := by
  classical

  have hmem : ∀ i (y : Y), y ∈ π ⁻¹ᵁ nonzeroLocus (σ i) ↔ gn y ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := by
    intro i y
    obtain ⟨j, hj⟩ := exists_chart hL (π y)
    obtain ⟨jA, hjA⟩ := exists_chart hLA (gn y)
    obtain ⟨u, hu⟩ := H y (fun _ => j) (fun _ => jA) hj hjA
    change π y ∈ nonzeroLocus (σ i) ↔ gn y ∈ nonzeroLocus (b i)
    rw [GlobalTheory.SectionRingIso.mem_iff_isUnit (σ i) π y (j := fun _ => j) hj,
      GlobalTheory.SectionRingIso.mem_iff_isUnit (b i) gn y (j := fun _ => jA) hjA]
    change IsUnit (secGerm π y (σ i) _) ↔ IsUnit (secGerm gn y (b i) _)
    rw [hu i, _root_.mul_assoc, IsUnit.mul_iff, IsUnit.mul_iff]
    simp only [u.isUnit, isUnit_gs_top p y (c i), true_and]
  have hW : ∀ i, π ⁻¹ᵁ nonzeroLocus (σ i) = gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := fun i =>
    TopologicalSpace.Opens.ext (Set.ext fun y => hmem i y)
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  ·
    refine eq_top_iff.2 fun y _ => ?_
    have : gn y ∈ ⨆ i, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := hb.1 ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hmem i y).2 hi⟩
  · rw [hW i]; exact (hb.2 i).1.preimage gn
  · obtain ⟨-, ρ, hρ, hs⟩ := hb.2 i
    have le : π ⁻¹ᵁ nonzeroLocus (σ i) ≤ gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) := (hW i).le
    have ge : gn ⁻¹ᵁ ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) ≤ π ⁻¹ᵁ nonzeroLocus (σ i) := (hW i).ge
    let φ : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)) →+* Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) :=
      (GlobalTheory.AbLaw.rs Y le).comp (gn.app _).hom
    have gsφ : ∀ y (hy : y ∈ π ⁻¹ᵁ nonzeroLocus (σ i)) (a : Γ(XA, (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i))),
        gs (𝟙 Y) y _ (φ a) = gs gn y _ a := fun y hy a =>
      (gs_res (𝟙 Y) y le hy _).trans ((gs_pull (𝟙 Y) gn y _ (le hy) a).trans (by rw [Category.id_comp]))
    have hφc : ∀ x : K, φ (GlobalTheory.AbLaw.cst pA _ x) = GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) x := fun x =>
      fn_ext fun y hy => by
        rw [gsφ y hy, gs_abCst pA _ gn y (le hy), gs_abCst p _ (𝟙 Y) y hy, hp, Category.id_comp]
    let r : Fin (m + 1) → Γ(Y, π ⁻¹ᵁ nonzeroLocus (σ i)) := fun j =>
      GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i)) ((c j : K) / c i) * φ (ρ j)
    refine ⟨r, ?_, ?_⟩
    · intro j ch a ha hch
      obtain ⟨jA, hjA⟩ := exists_chart hLA (gn a)
      obtain ⟨u, hu⟩ := H a ch (fun _ => jA) (GlobalTheory.SectionRingIso.mem_ch.1 hch) hjA
      have haW : a ∈ π ⁻¹ᵁ nonzeroLocus (σ i) := ha
      have haV : gn a ∈ (𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i) := le haW
      have hA : (𝟙 XA) (gn a) ∈ secChart LA (fun _ => jA) := GlobalTheory.SectionRingIso.mem_ch.2 hjA
      have key : ∀ j', secGerm gn a (b j') (fun _ => jA) =
          (gn.stalkMap a).hom (secGerm (𝟙 XA) (gn a) (b j') (fun _ => jA)) := fun j' => by
        have := secGerm_comp gn (𝟙 XA) a (b j') hA
        rwa [Category.comp_id] at this
      have e := congrArg (gn.stalkMap a).hom (hρ j (fun _ => jA) (gn a) haV hA)
      rw [map_mul, ← key, ← key, ← gs_stalkMap gn a _ haV] at e
      have hci : ((c j : K) / c i) * c i = c j := div_mul_cancel₀ _ (c i).ne_zero
      have hcst : gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c j : K)) =
          gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((c j : K) / c i)) *
            gs p a ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c i : K)) := by
        rw [← gs_top_mul, hci]
      rw [hu j, hu i, gs_mul (𝟙 Y) a _ haW, gs_abCst p _ (𝟙 Y) a haW, gsφ a haW, e, Category.id_comp, hcst]
      ring
    · intro f
      obtain ⟨g0, hg0⟩ := (ConcreteCategory.bijective_of_isIso (gn.app ((𝟙 XA) ⁻¹ᵁ nonzeroLocus (b i)))).2
        (GlobalTheory.AbLaw.rs Y ge f)
      have hf : φ g0 = f := by
        change GlobalTheory.AbLaw.rs Y le ((gn.app _).hom g0) = f
        rw [hg0, GlobalTheory.AbLaw.rs_rs, GlobalTheory.AbLaw.rs_self]
      obtain ⟨P, hP⟩ := hs g0
      have hcomp : φ.comp (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst pA _) ρ) =
          MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) (fun j => φ (ρ j)) :=
        MvPolynomial.ringHom_ext (fun x => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, hφc])
          (fun j => by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X'])
      have hρr : ∀ j, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst p (π ⁻¹ᵁ nonzeroLocus (σ i))) r
          (MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) = φ (ρ j) := fun j => by
        have h1 : ((c i : K) / c j) * ((c j : K) / c i) = 1 := by
          rw [div_mul_div_comm, _root_.mul_comm (c i : K)]
          exact div_self (mul_ne_zero (c j).ne_zero (c i).ne_zero)
        rw [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
        change GlobalTheory.AbLaw.cst p _ ((c i : K) / c j) * (GlobalTheory.AbLaw.cst p _ ((c j : K) / c i) * φ (ρ j)) = φ (ρ j)
        rw [← _root_.mul_assoc, ← map_mul, h1, map_one, _root_.one_mul]
      refine ⟨MvPolynomial.bind₁ (fun j => MvPolynomial.C ((c i : K) / c j) * MvPolynomial.X j) P, ?_⟩
      rw [MvPolynomial.eval₂Hom_bind₁]
      simp only [hρr]
      rw [← hf, ← hP, ← hcomp]
      rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgePropertyDescendsField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem wedgeO_descends_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → WedgeO (OAff B.hom) → WedgeO (OAff A.hom) := by
  intro K L _ _ _ A _ B _ φ h hA hB
  have hp : IsProper A.hom := hA.proper
  obtain ⟨⟨e₁, he₁⟩, e₂, he₂⟩ :=
    _root_.GlobalTheory.AbCoh.flat_baseChange_HO K L A.left B.left A.hom B.hom φ h.1 inferInstance inferInstance
  refine _root_.GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange K L _ _ _ _ (cup (OAff A.hom)) (cup (OAff B.hom)) e₁ e₂ (fun a b ↦ ?_) hB
  rw [he₁, he₁, he₂]
  exact (_root_.GlobalTheory.AbCoh.pull_comp_cup_id.2.1 K L A.left B.left A.hom B.hom _ φ h.1.w).1 a b

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDz
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.LineForm

theorem chain_sum_coordVec {n : ℕ} (w : V n) : w = ∑ b, w b • coordVec b := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem del_dbar_comp_holo_pull : ∀ (m n : ℕ) (τ : V m → V n) (c : V n → ℂ) (v : V m),
    DifferentiableAt ℂ τ v → DifferentiableAt ℝ c (τ v) →
    (∑ a, del (fun x => c (τ x)) v (coordVec a) • dz a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, del c (τ v) (coordVec a) • dz a) ∧
    (∑ a, dbar (fun x => c (τ x)) v (coordVec a) • dzb a : Alt m)
      = pull (fderiv ℂ τ v) (∑ a, dbar c (τ v) (coordVec a) • dzb a) := by
  intro m n τ c v hτ hc
  constructor
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [del_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [dbar_comp_holo hc hτ, map_sum, map_smul, (pull_dz _ _).2, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [chain_sum_coordVec (fderiv ℂ τ v (coordVec a))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smulₛₗ, Finset.sum_smul, smul_smul, smul_eq_mul, mul_comm]

end GlobalTheory.LineForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Taut

theorem X_mem_nonZeroDivisors (W : Type) [CommRing W] {σ : Type} (k : σ) :
    (MvPolynomial.X k : MvPolynomial σ W) ∈ nonZeroDivisors (MvPolynomial σ W) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun p hp => ?_, fun p hp => ?_⟩
  · ext m
    have := congrArg (AddMonoidAlgebra.coeff · (m + Finsupp.single k 1)) hp
    rwa [mul_comm, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this
  · ext m
    have := congrArg (AddMonoidAlgebra.coeff · (m + Finsupp.single k 1)) hp
    rwa [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this

theorem monomial_chart : ∀ {o : Type} [CommRing o] {ζ : o} (g n : ℕ) (φ : InvFun ℤ), 1 ≤ n → ∀ C : Taut ζ g n φ,
    C.Q.IsMonomialTau C.t (fun k => (n : ℤ) • C.δ k) ∧ Module.finrank ℤ C.Q.X ≤ g ∧ IsCone id φ C.δ ∧
      (∀ z, z ≠ 0 → ∃ k, 0 < C.δ k z z) ∧ (∀ k, C.t k ≠ 0) := by
  intro o _ ζ g n φ _ C
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    obtain ⟨k, hk, hc⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator C.T (C.ψ.comp MvPolynomial.C) (fun k => C.ψ (MvPolynomial.X k))
      (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.Q C.e C.data a b
    let z : Fin C.N → ℤ := fun j => (n : ℤ) * (C.ε (.inr j) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)
    let w : C.Rˣ := ∏ j, (C.tor j).unit ^ z j
    refine ⟨k * Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹, ?_,
      GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
    rw [Units.val_mul, hk, Fintype.prod_sum_type]
    have hw : ((Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹ : (FractionRing C.R)ˣ) : FractionRing C.R) *
        ∏ j : Fin C.N, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inr j))) ^ z j = 1 := by
      rw [← Units.val_one, ← mul_inv_cancel (Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w)]
      simp [w, map_prod, Units.coe_prod, map_zpow]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ?_)
      exact (map_ne_zero_iff _ (IsFractionRing.injective C.R (FractionRing C.R))).2 (C.tor j).ne_zero
    have hl : ∏ i, algebraMap C.R (FractionRing C.R) (C.t i) ^ (((n : ℤ) • C.δ i) a b) =
        ∏ k : Fin C.m, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inl k))) ^
          ((n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)) := by
      rfl
    rw [hl, _root_.mul_assoc, mul_comm (∏ j : Fin C.N, _), hw, _root_.mul_one]
  · have h : Module.finrank ℤ C.Q.X = C.T.r := by
      rw [C.e.toIntLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    have := C.genus
    omega
  · exact C.cone.pull_equiv C.e.toIntLinearEquiv
  · intro z hz
    obtain ⟨k, hk⟩ := C.defin (C.e z) (by simpa using hz)
    exact ⟨k, hk⟩
  · intro k hk
    letI := C.ψ.toAlgebra
    haveI : Module.Flat (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R := C.compl.2.2.1
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C.R) (X_mem_nonZeroDivisors C.W (Sum.inl k : Fin C.m ⊕ Fin C.N))
    apply one_ne_zero (α := C.R)
    apply hreg
    show C.ψ (MvPolynomial.X (.inl k)) * 1 = C.ψ (MvPolynomial.X (.inl k)) * 0
    rw [show C.ψ (MvPolynomial.X (.inl k)) = 0 from hk]; simp

end GlobalTheory.TChart.Taut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

def LatTo {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (𝔪 : UMem X₁ z₁ act V ev X t δ) : Prop :=
  ∃ K : (Fin 8 → X₀) ≃+ (Fin 8 → X), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀),
      K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) ∧ ∀ a mu, 𝔪₀.YY a mu → 𝔪.YY a (K mu)


open Classical in
def ZHAbove (X₁ : Setup F W i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) : Prop :=
  ∃ (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J), Nonempty (ZHOut X₁.ρ Y U₀ EE) ∧ X₁.S.Over₀ Y U₀ ∧ X₁.S.IsEE Y U₀ EE ∧
    X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY

theorem LatTo.refl {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) : LatTo 𝔪 𝔪 :=
  ⟨AddEquiv.refl _, fun _ _ => rfl, fun _ _ h => h⟩

theorem LatTo.trans {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁}
    {X₂ : Type} [AddCommGroup X₂] {m₁ : ℕ} {t₁ : Fin m₁ → V₁} {δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₂}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    {𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪₁ : UMem X₁ z₁ act V₁ ev₁ X₂ t₁ δ₁} {𝔪 : UMem X₁ z₁ act V ev X t δ}
    (h₀ : LatTo 𝔪₀ 𝔪₁) (h₁ : LatTo 𝔪₁ 𝔪) : LatTo 𝔪₀ 𝔪 := by
  obtain ⟨K₀, e₀, l₀⟩ := h₀
  obtain ⟨K₁, e₁, l₁⟩ := h₁
  refine ⟨K₀.trans K₁, fun a mu => ?_, fun a mu h => l₁ _ _ (l₀ _ _ h)⟩
  simp only [AddEquiv.trans_apply]
  rw [e₀, e₁]

end GlobalTheory.Poinc.Sep.Cmp
end
end

