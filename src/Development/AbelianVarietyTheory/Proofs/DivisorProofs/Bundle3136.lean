module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogVectorFieldMemMaxIdealSmulOfVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOfSmall
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCountStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  first | (exact @GlobalTheory.HTCount.count) | (exact GlobalTheory.HTCount.count) | (intros; apply GlobalTheory.HTCount.count  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.obj_lift_sqZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  intro p _ D R _ b N _ hN A₁ A₀ _ _ _ _ π β hπ hk o
  have hc : spMap (π.comp β) = spMap π ≫ spMap β := by
    simp only [spMap, Sp, CommRingCat.ofHom_comp, Spec.map_comp]
  have hk2 : RingHom.ker π ^ 2 = ⊥ := by rw [pow_two]; exact hk
  revert o
  rw [hc]
  intro o
  first
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N hN A₁ A₀ π hπ hk2 (spMap β) o
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N A₁ A₀ π hπ hk2 (spMap β) o
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KollarTwoPointSeparationOfNadelVanishing
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem pointSeparationPair_of_vanishing :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics →
      GlobalTheory.Published.PointSeparationPair := by
  intro hP hV hN X _ _ _ p n hproj hdim M Δ m G r N₀ x₁ x₂ c hM hΔ hklt hm hG hr hnef hbig hC
    h₁ h₂ hx hc hZ hs
  letI := algebraΓOfHom p
  obtain ⟨h, hpos, hsum, hh⟩ := _root_.GlobalTheory.PairStep.exists_rat_budgets n r c hr hc hs
  have hr' : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr
  refine GlobalTheory.T.separate_two_points_nef_big hP hV hN X p n hproj hdim M Δ m G N₀ (1 / (r : ℚ)) h x₁ x₂ hM hΔ hklt hm hG
    hnef hbig ?_ h₁ h₂ hx hpos ?_ hsum (by positivity)
  · intro C hCc
    rw [hC C hCc]
    ring
  · intro z e hz he hze
    have hle : e ≤ n := by
      have h1 := topologicalKrullDim_subspace_le X (closure ({z} : Set X))
      rw [hze, hdim] at h1
      exact_mod_cast h1
    have hmem : x₁ ∈ Closeds.closure ({z} : Set X) ∨ x₂ ∈ Closeds.closure ({z} : Set X) := by
      rcases hz with hz | hz
      · exact Or.inl (specializes_iff_mem_closure.1 hz)
      · exact Or.inr (specializes_iff_mem_closure.1 hz)
    have hZ' := hZ (Closeds.closure ({z} : Set X)) e isIrreducible_singleton.closure hmem he hze
    exact hh e (Finset.mem_Icc.2 ⟨he, hle⟩) _ hZ'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_locally_acyclic : GlobalTheory.EtC.C5 := by
  first | (exact @GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (exact GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing) | (intros; apply GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerInjectiveModMaximalBoundary
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

def constEps {σ k : Type} [Field k] (δ : Derivation ℤ (MvPowerSeries σ k) (MvPowerSeries σ k)) :
    MvPowerSeries σ k →+* DualNumber k where
  toFun r := TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (δ r))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [Derivation.leibniz, mul_comm, add_comm]

theorem constEps_apply {σ k : Type} [Field k] (δ : Derivation ℤ (MvPowerSeries σ k) (MvPowerSeries σ k))
    (r : MvPowerSeries σ k) :
    constEps δ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) +
      TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (δ r)) := rfl

theorem residue_eq_zero_iff_constantCoeff {σ k : Type} [Field k] (r : MvPowerSeries σ k) :
    residue _ r = 0 ↔ MvPowerSeries.constantCoeff r = 0 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]

theorem logKS_inj_mod_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x, x ∉ interior Y ∧ x ∈ U.1 ∧ ∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → D ∈ m • (⊤ : Submodule Γ(Y.X, U.1) (logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hvb hA D Θ m hm hx hKS hΘ
  obtain ⟨x, hxi, hxU, hxm⟩ := hx
  have h2 := _root_.GlobalTheory.BoundaryPoint.exists_closed_boundary_point E H Dw l Xo c Y hsm U m hm x hxi hxU hxm
  obtain ⟨x', hx'x, hx'bd, hx'cl⟩ := h2
  have h3 := hrig x' hx'bd hx'cl
  obtain ⟨k, _, m', d, ξ, t, P, gam, hξ, hEt, hId, hBd, hSAB, hMon, hPart, hRig⟩ := h3
  have hxU' : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := by
    show genι Y (ξ (closedPoint _)) ∈ U.1
    rw [hξ, hx'x]
    exact hxU
  have hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1 := top_le_preimage_of_closedPoint _ _ hxU'
  have h4 := GlobalTheory.ChartDer.logDer_extend_chartRing E H Dw l Xo c Y U D k m' d ξ hxU' hEt hId
  obtain ⟨DR, hDR0, hDRt⟩ := h4
  have hval : ∀ r, valR (ξ ≫ genι Y) U.1 r = ((Scheme.stalkClosedPointTo ξ).hom.comp
      (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hxU').hom.comp ((genι Y).app U.1).hom)) r := by
    intro r
    have e := ReciprocityTheory.ChartRestriction.G.PullbackSections.germ_stalkClosedPointTo_eq ξ (genι Y ⁻¹ᵁ U.1) hxU'
    have e2 := congrArg (fun φ => φ.hom (((genι Y).app U.1).hom r)) e
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [RingHom.comp_apply, RingHom.comp_apply, e2, valR, dite_eq_left hU, Scheme.Hom.comp_appLE]
    rfl
  have hDR : ∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r) := by
    intro r
    rw [hval, hval]
    exact hDR0 r
  have ha' : ∀ i, ∃ a, DR (bdParam k m' d i) = a * bdParam k m' d i := fun i => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hDRt i)
    exact ⟨a, ha.symm⟩
  choose a ha using ha'
  have hc := _root_.GlobalTheory.ChartConst.isConstAlong_of_ks_mem E H Dw l Xo c Y hpq hsm hsnc U n v A hv hvb hA D Θ m hm x hxi hxU hxm hKS hΘ k m' d ξ x' hξ
    hx'x t P gam hEt hId hBd hSAB hMon hPart hU DR a hDR ha (constEps DR) (constEps_apply DR)
  obtain ⟨c₀, hc₀, hcc⟩ := hc
  have ht0 : ∀ i, MvPowerSeries.constantCoeff (bdParam k m' d i) = 0 := fun i => by simp
  have hsnd : ∀ r, (constEps DR r).snd = 0 := by
    have h1 : ∀ r ∈ maximalIdeal (ChartRing k m' d), (constEps DR r).fst = 0 := fun r hr => by
      rw [constEps_apply]
      simpa using (residue_eq_zero_iff_constantCoeff r).1 ((residue_eq_zero_iff r).2 hr)
    have h2 : ∀ i, constEps DR (bdParam k m' d i) = 0 := fun i => by
      rw [constEps_apply, ha i, map_mul, ht0 i, mul_zero]
      simp
    exact hRig k (constEps DR) _ h1 h2 hcc
  have hres : ∀ r, residue _ (DR r) = 0 := fun r => by
    rw [residue_eq_zero_iff_constantCoeff]
    simpa [constEps_apply] using hsnd r
  haveI : CharZero k := by
    let f : c.F →+* k := MvPowerSeries.constantCoeff.comp (Spec.preimage (ξ ≫ genι Y ≫ Y.s)).hom
    exact charZero_of_injective_ringHom f.injective
  have hli : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    hPart.linearIndependent.map' (levelForms H l.M' P.D.toPre.X).subtype (Submodule.ker_subtype _)
  have hdir := GlobalTheory.ConstPointCone.dir_eq_zero_of_const (ChartRing k m' d) P.D.toPre m' (bdParam k m' d)
    (fun i => gam i) hMon hli (fun i => by simp [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff])
    (fun i y z => (gam i).2.1 y z) k (constEps DR) _ hsnd hcc
  have ha0 : ∀ i, residue _ (a i) = 0 := fun i => by
    rw [residue_eq_zero_iff_constantCoeff]
    have := congrFun hdir i
    simp only [Pi.zero_apply, mul_eq_zero, Rat.cast_eq_zero, hc₀, false_or] at this
    exact this
  exact _root_.GlobalTheory.LogBack.mem_smul_top_of_vanish E H Dw l Xo c Y hsm hsnc U D m hm x hxi hxU hxm k m' d ξ x' hξ hx'x hEt hId hBd hU DR a hDR ha
    hres ha0

end GlobalTheory.ChartDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocus
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem idemImage_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (Y : Scheme.{0}) (j : Y ⟶ S') (c : SiegPre h M (zetaAway M) (j ≫ t)), IsImmersion j ∧ QuasiCompact j ∧ SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(Y, ⊤)) ∧ (∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (y : T ⟶ Y) (c' : SiegPre h M (zetaAway M) t'), y ≫ j ≫ t = t' → SiegPB c' c y → ∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act (y ≫ j) ∧ ZRel e jl o κ c' w actw) ∧ ∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) t'), g ≫ t = t' → IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), ActPB w actw z act g ∧ ZRel e jl o κ c' w actw) → ∃! y : T ⟶ Y, y ≫ j = g ∧ SiegPB c' c y := by
  intro h h' M d O _ bar e jl n o κ S' _ t z act hh hM hodd hd hcop hpr hra hadj hee
  obtain ⟨U, c, wU, actU, hker, hunit, hwp, hwr, hwa, hwpb, hrel, hrange⟩ :=
    GlobalTheory.T.exists_open_locus_idempotent_image_siegel h h' M d O bar e jl n o κ S' t z act hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨U.toScheme, U.ι, c, inferInstance, inferInstance, hker, hunit, ?_, ?_⟩
  · intro T t' y c' hyt hc'
    obtain ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂⟩ :=
      GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback h' M (cycAway M) (zetaAway M) O bar U.toScheme T (U.ι ≫ t) t' y wU actU hyt hwp hwr hwa
    exact ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂.trans hwpb,
      GlobalTheory.T.idempotent_image_relation_of_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) t' y c wU actU c' w₂ act₂ hpb₂ hc' hrel⟩
  · intro T t' g c' hgt hdu hc' hex
    subst hgt
    have hr : Set.range g.base ⊆ (U : Set S') := hrange T g c' hdu hc' hex
    let y : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι g (by rw [Scheme.Opens.range_ι]; exact hr)
    have hy : y ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨w', actw', hpb', hrel'⟩ := hex
    refine ⟨y, ⟨hy, ?_⟩, ?_⟩
    · have hpb'' : ActPB w' actw' z act (y ≫ U.ι) := by rw [hy]; exact hpb'
      exact GlobalTheory.T.siegel_pullback_of_idempotent_images_and_action_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) (g ≫ t) y c wU actU c' w' actw'
        (_root_.GlobalTheory.UPel.HT.actPB_cancel h' M (cycAway M) (zetaAway M) O S' U.toScheme T t (U.ι ≫ t) (g ≫ t) z act U.ι y wU actU w' actw' hwpb hpb'')
        hrel hrel'
    · rintro y' ⟨hy', -⟩
      exact (cancel_mono U.ι).1 (hy'.trans hy.symm)

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToArtinian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegelArtin

theorem exists_socle (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C]
    (hm : IsLocalRing.maximalIdeal C ≠ ⊥) :
    ∃ e : C, e ≠ 0 ∧ e ∈ IsLocalRing.maximalIdeal C ∧ ∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0 := by
  set m := IsLocalRing.maximalIdeal C
  have hnil : IsNilpotent m := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
  have hex : ∃ k, m ^ k = ⊥ := by
    obtain ⟨k, hk⟩ := hnil
    exact ⟨k, by rw [hk]; rfl⟩
  classical
  let k := Nat.find hex
  have hk : m ^ k = ⊥ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0
    have : m ^ k = ⊤ := by rw [h0, pow_zero, Ideal.one_eq_top]
    rw [this] at hk
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp (hk ▸ bot_le))
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hk
    exact hm hk
  have hprev : m ^ (k - 1) ≠ ⊥ := Nat.find_min hex (by omega)
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprev
  refine ⟨e, he0, ?_, ?_⟩
  · exact Ideal.pow_le_self (by omega) he
  · intro a ha
    have : a * e ∈ m ^ k := by
      have hk' : k = (k - 1) + 1 := by omega
      rw [hk', pow_succ']
      exact Ideal.mul_mem_mul ha he
    rw [hk] at this
    simpa using this

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F
  suffices H : ∀ (N : ℕ) (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C],
      Module.length C C = N → ∀ (β : cycAway n →+* C) (c : SiegPre g n (zetaAway n) (spMap β)),
      c.Principal → ∃ f : Sp C ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f by
    intro C _ _ _ β c hc
    obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top (R := C) (M := C))
    exact H N C hN.symm β c hc
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C _ _ _ hN β c hc
  by_cases hm : IsLocalRing.maximalIdeal C = ⊥
  · letI : Field C := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm).toField
    exact _root_.GlobalTheory.SiegField.classify g n hg hn hodd F C β c hc
  obtain ⟨e, he0, hem, hann⟩ := exists_socle C hm
  set I : Ideal C := Ideal.span {e}
  have hIt : I ≠ ⊤ := by
    intro h
    have : I ≤ IsLocalRing.maximalIdeal C := (Ideal.span_singleton_le_iff_mem _).mpr hem
    rw [h] at this
    exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top (top_le_iff.mp this)
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIt
  haveI : IsLocalRing (C ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

  have hlenQ : Module.length C (C ⧸ I) = Module.length (C ⧸ I) (C ⧸ I) :=
    Module.length_eq_of_surjective (R := C ⧸ I) (S := C) (M := C ⧸ I) Ideal.Quotient.mk_surjective
  have hsum : Module.length C C = Module.length C I + Module.length C (C ⧸ I) :=
    Module.length_eq_add_of_exact I.subtype I.mkQ I.injective_subtype I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I)
  haveI : Nontrivial I := ⟨⟨⟨e, Ideal.subset_span rfl⟩, 0, fun h => he0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.length C I := Module.length_pos
  rw [hN, hlenQ] at hsum
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (show Module.length C I ≠ ⊤ from fun h => by
    rw [h, top_add] at hsum; exact ENat.natCast_ne_top _ hsum)
  obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (show Module.length (C ⧸ I) (C ⧸ I) ≠ ⊤ from fun h => by
    rw [h, add_top] at hsum; exact ENat.natCast_ne_top _ hsum)
  rw [← hb, ← hM] at hsum
  rw [← hb] at hpos
  have hb0 : 0 < b := by exact_mod_cast hpos
  have hNM : N = b + M := by exact_mod_cast hsum
  have hlt : M < N := by omega
  refine _root_.GlobalTheory.SmallClassify.classified_of_small g n hg hn hodd F C e hem hann β c hc ?_
  intro c₀ hpb
  have hcomm : spMap (Ideal.Quotient.mk I) ≫ spMap β = spMap ((Ideal.Quotient.mk I).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hc₀ : c₀.Principal :=
    (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp C) (Sp (C ⧸ I)) (spMap β)
      (spMap ((Ideal.Quotient.mk I).comp β)) (spMap (Ideal.Quotient.mk I)) c hcomm).2 c₀ hpb hc
  exact ih M hlt (C ⧸ I) hM.symm _ c₀ hc₀

end GlobalTheory.SiegelArtin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitChartGenericFibresSame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem sameFib_trait_chart : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  intro g n φ F C G₁ _ _ P hP hC T V' _ _ _ θ f fK hV' hθ hs hfK D' e hDF G' _ _ πG A' U' hU
  obtain ⟨G'', _, _, π, π₂, A'', U'', hπ, hπ₂, hΛ''⟩ := _root_.GlobalTheory.TChart.Taut.unif_pull_of_canonOn C G₁ P hP hC V' θ hV' hθ hs D' e hDF
  obtain ⟨hG', κ, πK, α, α₂, hκ, -, hα, hα₂, hΛ', -⟩ := hU

  have hκ' : κ = spMap fK := by
    haveI := GlobalTheory.Mum.EvenDesc.mono_jK T.V
    rw [← cancel_mono (jK T.V), hκ]
    have e₁ : (algebraMap V' (FractionRing V')).comp f = fK.comp (algebraMap T.V (FractionRing T.V)) :=
      RingHom.ext fun a => (hfK a).symm
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) e₁
  subst hκ'
  have hsG'' : IsSemiAbelian G'' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hP.2.2.1
  have hsG' : IsSemiAbelian G' := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hG' T.semi
  have hAdm : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  obtain ⟨hD, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self V' _ hAdm D'
  obtain ⟨ψ, hψm, hψL, -⟩ := GlobalTheory.exists_generic_iso_of_unif GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 V'
    (maximalIdeal V') hAdm (maximalIdeal.isMaximal V').ne_top D' D' A'' A' G'' G' hsG'' hsG' U'' U' hD
  haveI := hψm
  haveI := U''.gen_hom
  haveI : IsMonHom U''.gen.symm.hom := inferInstanceAs (IsMonHom U''.gen.inv)

  let b : A'.A.left ⟶ G''.left := ψ.hom.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (jK V')
  have hb : IsGrpPullback A'.A G'' (jK V') b :=
    ((isGrpPullback_of_iso ψ).comp ((isGrpPullback_of_iso U''.gen.symm).comp
      (isGrpPullback_pullback G'' (jK V')))).congr (by simp only [Category.id_comp]) rfl
  obtain ⟨b₂, hb₂, hΛb⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (jK V') G'' A'.A b hb
  have hPLB : P.IsLB := hP.2.2.2.1.1
  have hL : LBIso A'.L (U''.LG.L.pull b) :=
    LBIso.trans A'.isLB (pull_isLB A''.isLB _) (pull_isLB U''.LG.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp (ψ.hom.left ≫ U''.gen.inv.left)
        (by rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id])
        (by simp only [b, Category.assoc]) U''.ext)
  have hΛA : LBIso (abelian₂ A'.A A'.L) (P.pull (b₂ ≫ π₂)) :=
    hΛb U''.LG.L A'.L _ P π₂ U''.LG.isLB A'.isLB hPLB hL hΛ''
  have hθK : spMap ((algebraMap V' (FractionRing V')).comp θ) = jK V' ≫ spMap θ := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  refine ⟨A'.A, inferInstance, inferInstance, α, α₂, b ≫ π, b₂ ≫ π₂, hα, hα₂,
    (hb.comp hπ).congr hθK.symm rfl, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hπ₂.1, ← Category.assoc, hb₂.1, Category.assoc]
  · rw [Category.assoc, hπ₂.2, ← Category.assoc, hb₂.2, Category.assoc]
  · exact LBIso.trans (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hPLB _) hΛ'.symm hΛA

end GlobalTheory.TChart
end

