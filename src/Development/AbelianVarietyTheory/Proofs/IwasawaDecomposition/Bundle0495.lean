module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanCw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
section
noncomputable section

namespace GlobalTheory.UnifComp

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ptF_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    ptF z = spMap φ.toRingHom ≫ ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
    congr 1
    ext a
    exact (φ.commutes a).symm

theorem ptF_frBor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) : ptF z = ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]

attribute [local instance 1100] Subalgebra.algebra in
theorem liesOn_chart {h : GenFrEx Xo c} (C : GlobalTheory.Reg.FChart h) : LiesOn C.Z C.y := by
  intro s
  let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
  let s₀ : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
  have e : spMap C.R.val.toRingHom s₀ = η :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
  have h1 : ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
    have := liesOn_genFr h C.Z s₀
    rw [← ptF_frBor C.bor, ptF_frMap C.gen, Scheme.Hom.comp_apply, e] at this
    exact this
  have h2 : η ⤳ s := (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
  exact (h2.map (ptF C.y).continuous).mem_closed (isClosed_of_mem_irreducibleComponents _ C.Z.2) h1

attribute [local instance 1100] Subalgebra.algebra in
theorem exists_liesOn {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) : ∃ Z : Comp Xo c, ∀ x : (U.X k).dom, LiesOn Z (U.un k x) := by
  obtain ⟨-, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneComp.exists_comp_of_charts E H Dw l Xo c σ r U hU h k
  refine ⟨Z, fun x s => ?_⟩
  let : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) (U.un k x)
  rw [← hZ x C ψ z t hz hb, ptF_frBor hb, ptF_frMap hz, Scheme.Hom.comp_apply]
  exact liesOn_chart C _

theorem eq_of_carries {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} {h : GenFrEx Xo c} {k : U.Comp}
    {Z Z' : Comp Xo c} (hk : GlobalTheory.CompModel.CarriesGeneric U h k Z) (h' : ∀ x : (U.X k).dom, LiesOn Z' (U.un k x)) :
    Z' = Z := by
  obtain ⟨P, w, x, t, hw, ht⟩ := hk
  by_contra hne
  let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z' Z hne) (h' x s) ?_
  rw [← ptF_frBor ht, ptF_frMap hw, Scheme.Hom.comp_apply]
  exact liesOn_genFr h Z _

theorem exists_equiv_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → FnAlgClosed (Xo := Xo) (c := c) → ∃ q : U.Comp ≃ Comp Xo c, ∀ k (x : (U.X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF (U.un k x) s ∈ (q k).1 := by
  intro E _ _ _ H Dw l Xo c σ N U hσ hU _ hF
  obtain ⟨-, -, h, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  choose q hq using exists_liesOn U hU
  refine ⟨Equiv.ofBijective q ⟨fun k k' e => ?_, fun Z => ?_⟩, fun k x s => hq k x s⟩
  · obtain ⟨Z, hZ⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k'
    obtain rfl : Z = Z' := (eq_of_carries hZ (hq k)).symm.trans (e.trans (eq_of_carries hZ' (hq k')))
    obtain ⟨P, w, x, t, hw, ht⟩ := hZ
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact GlobalTheory.GeomConn.comp_eq_of_fnAlgClosed E H Dw l Xo c σ N U.toPj hσ hU hF h Z k k' x x'
      ⟨P, w, t, hw, ht⟩ ⟨P', w', t', hw', ht'⟩
  · obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model U hU h Z
    exact ⟨k, eq_of_carries hk (hq k)⟩

end GlobalTheory.UnifComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.TorRef TensorProduct

namespace GlobalTheory.NormalBaseChange

theorem exists_etale_of_isEtaleCompletion (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing A] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (het : IsEtaleCompletion (algebraMap A R)) (hfu : ((residue R).comp (algebraMap A R)).FormallyUnramified) :
    ∃ g : AdicCompletion (maximalIdeal A) A →+* R, g.comp (algebraMap A _) = algebraMap A R ∧
      @Algebra.Etale _ R _ _ g.toAlgebra := by
  obtain ⟨hflat, hmap, hfin⟩ := het
  set h := algebraMap A R with hh
  let D := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing D := AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : IsAdicComplete ((maximalIdeal A).map h) R := by rw [hmap]; infer_instance
  obtain ⟨g, hg⟩ := exists_adicCompletion_ringHom_extend (maximalIdeal A) h
  letI : Algebra D R := g.toAlgebra
  have hgA : ∀ a, g (algebraMap A D a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal D).map (algebraMap D R) = maximalIdeal R := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal A).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap D R) := ((local_hom_tfae _).out 1 3).mpr hmA.le
  have hres : ((residue R).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap A D) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite D (R ⧸ (maximalIdeal D).map (algebraMap D R)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap D R)).Finite
    rw [hmA]
    exact hres
  haveI : IsHausdorff ((maximalIdeal D).map (algebraMap D R)) R := by rw [hmA]; infer_instance
  haveI : Module.Finite D R := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  haveI : Module.Flat D R := by
    refine LocalFlat.flat_of_relationsLift R (I := maximalIdeal D)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.mp hflat
    have fg := (maximalIdeal A).fg_of_isNoetherianRing
    have hkerA : ∀ x : D, AdicCompletion.evalₐ (maximalIdeal A) n x = 0 ↔ x ∈ maximalIdeal D ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal D ^ n).map (algebraMap D R) = (maximalIdeal A ^ n).map (algebraMap A R) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal A ^ n).map (g.comp _) = _
      rw [hg]
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal A ^ n).map (algebraMap A R)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
      have hx : x - algebraMap A D a ∈ maximalIdeal D ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap D R x - h a ∈ (maximalIdeal A ^ n).map (algebraMap A R) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap D R x - g (algebraMap A D a) = algebraMap D R (x - algebraMap A D a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
      exact hx'
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R (maximalIdeal A ^ n)).toLinearEquiv
  haveI : Algebra.FormallyUnramified D (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap D (ResidueField R)).comp (algebraMap A D) = (residue R).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap A D) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified D R :=
    GlobalTheory.EtaleCompletionNormal.formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation D R :=
    (Algebra.FinitePresentation.of_finiteType (R := D) (A := R)).1 inferInstance
  exact ⟨g, hg, Algebra.Etale.of_formallyUnramified_of_flat⟩

end GlobalTheory.NormalBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.ShFam.OpenReg

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Transfer

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {x : Sp R ⟶ S'} {x' : Sp R ⟶ S}

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (h : A →+* B) :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem epsMul_over (s : R) : spMap (epsMul s) ≫ spMap (algebraMap R (DualNumber R)) =
    spMap (algebraMap R (DualNumber R)) := by
  rw [spMap_comp]
  congr 1
  ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_lift {T : Scheme.{0}} (q : T ⟶ S') (v : T ⟶ t.G.left) (hv : v ≫ t.G.hom = q ≫ f) :
    ∃ w : T ⟶ t'.G.left, w ≫ t'.G.hom = q ∧ w ≫ m.φ = v :=
  ⟨m.cart.1.lift v q hv, m.cart.1.lift_snd _ _ _, m.cart.1.lift_fst _ _ _⟩

theorem tan_iff (hx : x ≫ f = x') {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsTanAtG t x' (w ≫ m.φ) ↔ IsTanAtG t' x w := by
  subst hx
  have e : (1 : Over.mk x ⟶ t'.G).left ≫ m.φ = (1 : Over.mk (x ≫ f) ⟶ t.G).left :=
    congrArg (fun z => z.left) (map_one (pushHom m.cart (Over.mk x)))
  constructor
  · intro h
    refine ⟨hw, m.cart.1.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h.2.trans e.symm
    · have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
        RingHom.ext fun r => by simp
      rw [Category.assoc, hw, ← Category.assoc, spMap_comp, hid, Over.w]
      exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)
  · intro h
    refine ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw, Category.assoc], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ m.φ) h.2).trans e

theorem eig_iff {w : Sp (DualNumber R) ⟶ t'.G.left}
    (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : 𝓞 E) (s : R) :
    (w ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul s) ≫ w ≫ m.φ ↔
      w ≫ (t'.act.act a).left = spMap (epsMul s) ≫ w := by
  have e : (w ≫ m.φ) ≫ (t.act.act a).left = (w ≫ (t'.act.act a).left) ≫ m.φ := by
    rw [Category.assoc, Category.assoc, m.act]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc (spMap _)]; exact h
    · rw [Category.assoc, Over.w, Category.assoc, hw, ← Category.assoc, epsMul_over]
  · intro h
    rw [h, Category.assoc]

theorem prod_iff {q : Sp (DualNumber R) ⟶ S'} {q' : Sp (DualNumber R) ⟶ S} (hq : q ≫ f = q') {n : ℕ}
    {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (hv : ∀ i, v i ≫ t'.G.hom = q)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = q) :
    (∃ u : Fin n → (Over.mk q' ⟶ t.G), (∀ i, (u i).left = v i ≫ m.φ) ∧ ((List.ofFn u).prod).left = w ≫ m.φ) ↔
      ∃ u : Fin n → (Over.mk q ⟶ t'.G), (∀ i, (u i).left = v i) ∧ ((List.ofFn u).prod).left = w := by
  subst hq
  have push : ∀ u : Fin n → (Over.mk q ⟶ t'.G), ((List.ofFn u).prod).left ≫ m.φ =
      ((List.ofFn fun i => pushHom m.cart (Over.mk q) (u i)).prod).left := fun u => by
    have := map_list_prod (pushHom m.cart (Over.mk q)) (List.ofFn u)
    rw [List.map_ofFn] at this
    exact congrArg (fun z => z.left) this
  constructor
  · rintro ⟨u, hu, hw'⟩
    let u' : Fin n → (Over.mk q ⟶ t'.G) := fun i => Over.homMk (v i) (hv i)
    have e : u = fun i => pushHom m.cart (Over.mk q) (u' i) := funext fun i => Over.OverMorphism.ext (hu i)
    refine ⟨u', fun i => rfl, m.cart.1.hom_ext ?_ ?_⟩
    · rw [e] at hw'
      exact (push u').trans hw'
    · rw [Over.w, hw]; rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushHom m.cart (Over.mk q) (u i), fun i => ?_, (push u).symm⟩
    show (u i).left ≫ m.φ = _
    rw [hu]

theorem comb_iff (hx : x ≫ f = x') {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)}
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (cf : Fin n → R)
    {w : Sp (DualNumber R) ⟶ t'.G.left} (hw : w ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    IsCombAtG t x' (fun i => v i ≫ m.φ) cf (w ≫ m.φ) ↔ IsCombAtG t' x v cf w := by
  have := prod_iff m (q := spMap (algebraMap R (DualNumber R)) ≫ x) (q' := spMap (algebraMap R (DualNumber R)) ≫ x')
    (by rw [Category.assoc, hx]) (v := fun i => spMap (epsMul (cf i)) ≫ v i)
    (fun i => by rw [Category.assoc, hv, ← Category.assoc, epsMul_over]) hw
  simp only [Category.assoc] at this
  exact this

end Transfer

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β}

theorem exists_frPt_of_eigFrame {R : Type} [CommRing R] [IsLocalRing R] [Algebra c.F R] (xF : Sp R ⟶ Xo.XF c)
    (hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R)) {x : Sp R ⟶ Z.X} (hx : xF ≫ Z.jQ ≫ pullback.fst _ _ = x)
    (f : EigFrame Z (algebraMap c.F R) x) :
    ∃ (y : FrPt Xo c R) (w : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.oF.t.G.left)),
      y.x = xF ≫ pullback.fst _ _ ∧ ∀ τ i, w τ i ≫ Z.oF.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ xF ∧
        w τ i ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w τ i ≫ Z.m.φ = f.v τ i := by
  have hover : (xF ≫ pullback.fst _ _) ≫ Xo.s = sOf c R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp]; rfl
  obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frPt (c := c) _ hover
  choose w hw1 hw2 using fun τ i => exists_lift Z.m (spMap (algebraMap R (DualNumber R)) ≫ xF) (f.v τ i)
    (by rw [(f.tan τ i).1, ← hx, Category.assoc])
  refine ⟨⟨z.x, z.x_over, fun τ i => w τ i ≫ Z.m0.toSABMap.φ, fun τ i => ?_, fun τ i a => ?_, fun τ v hv he => ?_,
    z.s, z.gen⟩, w, hz, fun τ i => ⟨hw1 τ i, rfl, hw2 τ i⟩⟩
  · exact (tan_iff Z.m0.toSABMap hz.symm (hw1 τ i)).2 ((tan_iff Z.m hx (hw1 τ i)).1 (hw2 τ i ▸ f.tan τ i))
  · exact (eig_iff Z.m0.toSABMap (hw1 τ i) a _).2 ((eig_iff Z.m (hw1 τ i) a _).1 (hw2 τ i ▸ f.eig τ i a))
  · obtain ⟨v', h1, rfl⟩ := exists_lift Z.m0.toSABMap (spMap (algebraMap R (DualNumber R)) ≫ xF) v
      (by rw [hv.1, hz, Category.assoc])
    have hb := f.basis τ (v' ≫ Z.m.φ) ((tan_iff Z.m hx h1).2 ((tan_iff Z.m0.toSABMap hz.symm h1).1 hv))
      fun a => (eig_iff Z.m h1 a _).2 ((eig_iff Z.m0.toSABMap h1 a _).1 (he a))
    have e : f.v τ = fun i => w τ i ≫ Z.m.φ := funext fun i => (hw2 τ i).symm
    rw [e] at hb
    exact (existsUnique_congr fun cf => (comb_iff Z.m0.toSABMap hz.symm (hw1 τ) cf h1).trans
      (comb_iff Z.m hx (hw1 τ) cf h1).symm).2 hb

variable {F : Type} [Field F] {e : F ≃+* c.F}

theorem mono_spMap_algebraMap (A K : Type) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Mono (spMap (algebraMap A K)) := by
  have : IsPreimmersion (spMap (algebraMap A K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  infer_instance

end GlobalTheory.ShFam.OpenReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitTwistPlaceOverProductCharacterRamifie
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistSplitPlace

theorem isSplitPl_of_not_isConjPl (D : D7) (P : PlE D.host) (h : ¬ Formalism.IndefR.Lev.IsConjPl P P) : IsSplitPl D.host P := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun y hy hm => h y hm (hy.trans (GlobalTheory.DimPartsCompare.star_conj _).symm)⟩

theorem exists_splitPlace_of_mem_qPl : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (i : Fin D.R.m) (t : T), ∀ v ∈ qPl D (L.C.mu0 i * L.xiH t), ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
  rintro D T L μ0 hL i t v ⟨hg, w, hw, hn⟩
  have hu : (L.C.mu0 i).UnrAt w := (L.C.isMu0 i).unr w fun k hk => hg ⟨w, hw, k, hk⟩
  have hx : ¬ (L.xiH t).UnrAt w := fun h => hn fun x hx => by
    simpa [Host.HChar.loc] using congrArg₂ (· * ·) (hu x hx) (h x hx)
  have key : ∀ P ∈ L.Q t, NG.OverPl P v → ∃ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.v = v ∧ s.w ∈ L.Q t := by
    intro P hP hov
    obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D P
      (isSplitPl_of_not_isConjPl D P ((hL.Q_pl t P hP).2 P hP))
    refine ⟨s, HeightOneSpectrum.ext ?_, hs ▸ hP⟩
    rw [← s.w_under, hs]
    exact hov
  rcases (hL.Q_ram t w).1 hx with h | ⟨P, hP, hc⟩
  · exact key w h hw
  · refine key P hP ?_
    rw [GlobalTheory.DimPartsCompare.eq_cPl_of_isConjPl hc]
    exact (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.DimPartsCompare.under_cPl w)).trans hw

end GlobalTheory.TwistSplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionState
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem st_of_fits : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), ∀ o : P.q.Over, o.Fits → o.G = P.Z₀.G → o.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) → BkLaw (w.D o.Z) → ∃ x : St P, x.o = o := by
  intro hW hD hH hC K B f T w P o hfit hG heta hbk
  obtain ⟨m, hcopy, hcoh⟩ := GlobalTheory.T.exists_movedRowLiftData_to_fittingStages B f T w P.Z₀ P.hX P.Wt P.z P.q o P.intersectionNumber_baseChange P.exAt P.inGeo P.grp hfit
  obtain ⟨s, r, hpin⟩ := _root_.GlobalTheory.Mem.R3.Rw.readPk_pin_exists B f T w P.Z₀ P.hX P.Wt P.z P.q o
    (GlobalTheory.LinksInputs.inputs_of_hypotheses hW hD hH hC (w.D o.Z)) hfit m
  exact ⟨⟨o, hfit, hG, heta, hbk, m, hcopy, hcoh, s, r, hpin⟩, rfl⟩

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodFormsLiftBaseLevelExtensionSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem goodForms_lift_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        z'.R.toRealDat.WL z'.F.lv2 false j' = Submodule.span (w'.st Z').toD7.what₂.LL {x' | ∃ x ∈ z.R.toRealDat.WL z.F.lv2 false j, ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)}) := by
  intro p1 p2 p3 p4 p5 p6 p7
  have H := StepW.and (StepW.and (_root_.GlobalTheory.Mem.R3.RhoExt.rho_ext p1 p2 p3 p4 p5 p6 p7) (_root_.GlobalTheory.Mem.R3.ChiExt.chi_ext p1 p2 p3 p4 p5 p6 p7))
    (StepW.and (_root_.GlobalTheory.Mem.R3.Rw.extN_baseLevel_bc p1 p2 p3 p4 p5 p6 p7) (_root_.GlobalTheory.Mem.R3.GoodIdemBC.idemOf_coeff_ext p1 p2 p3 p4 p5 p6 p7))
  refine StepW.trans H (StepW.of_all fun K B' f' T' w' _ _ hq => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S1 := hq.1.1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S2 := hq.1.2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S3 := hq.2.1 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  have S4 := hq.2.2 B f T w hE hf hP hpx Z hX Wt z hG hGA hF hH Z' hX' hG' hGA' hV z' hF' hEx j j' hj φ hφ
  obtain ⟨e, he⟩ := GlobalTheory.Mem.R3.GoodBC.gc_iso B B' hE.1 w.px w'.px hpx
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := congrArg (fun P : Pre => P.R.m) hE.1
  have hn : z.R.nW j = z'.R.nW j' := (GlobalTheory.Mem.R3.GoodBC.nat_heq_app hm _ _ hEx.nW j j' hj).symm
  unfold RealDat.WL
  refine GlobalTheory.Mem.R3.GoodBC.wgood_bc_rel hn (z.R.toRealDat.FW j) (z'.R.toRealDat.FW j') φ e _ _ _ _ _ _
    (fun g x x' hx k k' hk => S1 g (e g) (he g) x x' hx k k' hk) (fun g => S2 g (e g) (he g))
    (fun g => (S3 g (e g) (he g)).1) (fun g hg hg' => ?_) (fun g => S4 g (e g) (he g))
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀,
    (S3 g (e g) (he g)).2 hg hg']

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCuspFormSpaceThetaMapEqDataStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ThDef3 D A3.A (A3.indefDown (s0Of R F)) Y.tup Y.eMt Z.jW ∧ ∀ (i : Fin D.R.m) (t : T) x, D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)) = Z.jW i (((A3.indefDown (s0Of R F)).θ i t).mulVec ((lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t).mulVec x)) := by
  first | exact @GlobalTheory.Mem.ThRead.thDef3_thTheta | exact GlobalTheory.Mem.ThRead.thDef3_thTheta | (intros; apply GlobalTheory.Mem.ThRead.thDef3_thTheta <;> assumption)
end

