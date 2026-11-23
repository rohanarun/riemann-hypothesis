module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealDivisibleEqZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpaces
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem exists_indicator_function {X : Scheme.{0}} (U : Set X) (hU : IsClopen U) :
    ∃ e : Γ(X, ⊤), e * e = e ∧ ∀ x : Sp ℂ ⟶ X,
      (x (IsLocalRing.closedPoint ℂ) ∈ U → valAt' x ⊤ e = 1) ∧
      (x (IsLocalRing.closedPoint ℂ) ∉ U → valAt' x ⊤ e = 0) := by
  let V : Bool → X.Opens := fun b => match b with
    | true => ⟨U, hU.2⟩
    | false => ⟨Uᶜ, hU.1.isOpen_compl⟩
  let sf : ∀ b, Γ(X, V b) := fun b => match b with
    | true => 1
    | false => 0
  have hcov : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : x ∈ U
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have hsub : ∀ W : X.Opens, W = ⊥ → Subsingleton Γ(X, W) := by
    rintro _ rfl
    infer_instance
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro a b
    cases a <;> cases b
    · simp [sf]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · simp [sf]
  obtain ⟨e, he'⟩ : ∃ e : Γ(X, ⊤), ∀ b, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e = sf b :=
    (X.sheaf.existsUnique_gluing' V ⊤ (fun b => homOfLE le_top) hcov sf hcomp).exists
  have hpt : ∀ (x : Sp ℂ ⟶ X) (b : Bool), x (IsLocalRing.closedPoint ℂ) ∈ V b → ⊤ ≤ x ⁻¹ᵁ V b := by
    intro x b h z _
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) z (IsLocalRing.closedPoint ℂ)]
  refine ⟨e, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine X.sheaf.eq_of_locally_eq' V ⊤ (fun b => homOfLE le_top) hcov _ _ fun b => ?_
    show X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op (e * e) = X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e
    rw [map_mul, he']
    cases b <;> simp [sf]
  · refine (TB.ValAt.valAt'_res x le_top (hpt x true h) e).symm.trans ((congrArg (valAt' x _) (he' true)).trans ?_)
    exact TB.ValAt.valAt'_one x _ (hpt x true h)
  · refine (TB.ValAt.valAt'_res x le_top (hpt x false h) e).symm.trans ((congrArg (valAt' x _) (he' false)).trans ?_)
    exact (valHom x _ (hpt x false h)).map_zero

theorem eq_val_of_A_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (σ : KA l →+* ℂ) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1) : σ = (KA l).val.toRingHom := by
  have hz : zeta l.A = 1 := by
    rw [hA, zeta, Nat.cast_one, div_one, Complex.exp_two_pi_mul_I]
  ext ⟨x, hx⟩
  show σ ⟨x, hx⟩ = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hσ
    · have : (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1 := Subtype.ext hz
      exact (congrArg σ this).trans ((map_one σ).trans hz.symm)
  | algebraMap q => exact (map_ratCast σ q)
  | add x y hx hy h1 h2 => exact (map_add σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | mul x y hx hy h1 h2 => exact (map_mul σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | inv x hx h1 => exact (map_inv₀ σ ⟨x, hx⟩).trans (by rw [h1])

theorem exists_coeff_idempotent_functions :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ hσ _ hA c
  obtain rfl := eq_val_of_A_eq_one σ₀ hσ hA
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c'
  let σ : c'.F →+* ℂ := c'.F.val.toRingHom
  let s : Xo.XF c' ⟶ Sp c'.F := pullback.snd _ _
  let pr : Xo.XF c' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨e, h1, h2⟩ := exists_indicator_function U hU
  refine ⟨e, h1, fun i' P hP p hp1 hp => ?_⟩
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := hp1
    rw [this]
    exact ht i' P hP
  split_ifs with h
  · subst h
    exact (h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩
  · refine (h2 p).2 ?_
    rintro ⟨q, hq, hqp, hqi⟩
    exact h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPoints
section
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace ComplexTransfer

theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem countable_of_finiteType (K A : Type) [CommRing K] [Countable K] [CommRing A] [Algebra K A]
    [h : Algebra.FiniteType K A] : Countable A := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  haveI : Countable (MvPolynomial (Fin n) K) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    simp
  exact hf.countable

theorem exists_common_field {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) {A B k : Type} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] [Countable A] [Countable B] [Field k] [Algebra K k]
    (φ : A →ₐ[K] k) (ψ : B →ₐ[K] k) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (ι : L →ₐ[K] k) (j : L →ₐ[K] CAt σ) (φL : A →ₐ[K] L)
      (ψL : B →ₐ[K] L), ι.comp φL = φ ∧ ι.comp ψL = ψ ∧ Function.Injective j := by
  let s : Set k := Set.range φ ∪ Set.range ψ
  have hs : s.Countable := (Set.countable_range _).union (Set.countable_range _)
  let L := IntermediateField.adjoin K s
  have hL : Countable L := by
    have := hs.to_subtype
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le K s).trans ?_
    simp
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨j⟩ := GlobalTheory.nonempty_algHom_complex_of_countable K L
  refine ⟨L, inferInstance, inferInstance, L.val, j,
    φ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inl ⟨a, rfl⟩),
    ψ.codRestrict L.toSubalgebra fun a => IntermediateField.subset_adjoin K s (Or.inr ⟨a, rfl⟩), ?_, ?_, ?_⟩
  · ext a; rfl
  · ext a; rfl
  · exact j.toRingHom.injective

theorem evalAt_of_mapR {K : Type} [Field K]
    (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
    (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
      (S →ₐ[K] T) → pts S → pts T → Prop)
    (hW : EvalWD pts mapR) (f : Rules pts) (hf : IsNatural pts mapR f)
    {S : Type} [CommRing S] [Algebra K S] (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R) (z : pts S)
    (hz : mapR φ y z) : evalAt pts mapR f z = φ (f p y) := by
  have hT : FromTest pts mapR z := ⟨p, φ, y, hz⟩
  unfold evalAt
  rw [dite_eq_left hT]
  exact (hW f hf S p _ φ _ y _ z hz hT.choose_spec.choose_spec.choose_spec).symm

end ComplexTransfer

theorem exists_complex_framed_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), ∃ z z' : FrPt Xo c (CAt c.F.val.toRingHom), (∀ ρ : Xo.X ⟶ Xo.X, y'.x = y.x ≫ ρ → z'.x = z.x ≫ ρ) ∧ (∀ f ∈ sec Xo c 0 0, evR Xo c f y = 0 → evR Xo c f z = 0) ∧ ∀ f ∈ sec Xo c 0 0, ∀ a : c.F, evR Xo c f z' = algebraMap c.F (CAt c.F.val.toRingHom) a * evR Xo c f z → evR Xo c f y' = algebraMap c.F k a * evR Xo c f y := by
  intro E _ _ _ H Dw l Xo c k _ _ y y'
  have hS : Out.SecBaseChangeSt := GlobalTheory.firstFiveLaws.1.secBaseChange
  have hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c))
  have hA : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  obtain ⟨p, φ, y₀, hy⟩ := hA k y
  obtain ⟨q, ψ, y₁, hy'⟩ := hA k y'
  haveI := c.fin
  haveI : Countable c.F := ComplexTransfer.countable_of_finiteType ℚ c.F
  haveI : Countable p.R := ComplexTransfer.countable_of_finiteType c.F p.R
  haveI : Countable q.R := ComplexTransfer.countable_of_finiteType c.F q.R
  obtain ⟨L, _, _, ι, j, φL, ψL, hφ, hψ, hj⟩ :=
    ComplexTransfer.exists_common_field c.F.val.toRingHom φ ψ
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp φL) y₀
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ (j.comp ψL) y₁
  have hι : Function.Injective ι := ι.toRingHom.injective
  have ev : ∀ f ∈ sec Xo c 0 0, evR Xo c f y = ι (φL (f p y₀)) ∧ evR Xo c f y' = ι (ψL (f q y₁)) ∧
      evR Xo c f z = j (φL (f p y₀)) ∧ evR Xo c f z' = j (ψL (f q y₁)) := by
    intro f hf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← AlgHom.comp_apply, hφ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p φ y₀ y hy
    · rw [← AlgHom.comp_apply, hψ]
      exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q ψ y₁ y' hy'
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 p _ y₀ z hz
    · exact ComplexTransfer.evalAt_of_mapR _ _ hW f hf.1 q _ y₁ z' hz'
  refine ⟨z, z', ?_, ?_, ?_⟩
  · intro ρ h
    have e1 : y.x = spMap ι.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy.1, ← hφ]; rfl
    have e2 : y'.x = spMap ι.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hy'.1, ← hψ]; rfl
    have e3 : z.x = spMap j.toRingHom ≫ spMap φL.toRingHom ≫ y₀.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz.1]; rfl
    have e4 : z'.x = spMap j.toRingHom ≫ spMap ψL.toRingHom ≫ y₁.x := by
      rw [← Category.assoc, ← Geo.Tor.spMap_comp, hz'.1]; rfl
    haveI := ComplexTransfer.epi_spMap_field ι.toRingHom
    rw [e1, e2, Category.assoc, cancel_epi] at h
    rw [e3, e4, h]
    simp only [Category.assoc]
  · intro f hf h
    obtain ⟨h1, -, h3, -⟩ := ev f hf
    rw [h1, map_eq_zero_iff ι hι] at h
    rw [h3, h, map_zero]
  · intro f hf a h
    obtain ⟨h1, h2, h3, h4⟩ := ev f hf
    rw [h3, h4, ← j.commutes, ← map_mul] at h
    rw [h1, h2, hj h, map_mul, ι.commutes]

end GlobalTheory.Frames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponent
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem onto_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem onto_adelic_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L Λ : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hLs : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hΛ : Λ.FG) (hΛs : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    {A B : Type} [AddCommGroup A] [Module (𝓞 E) A] [AddCommGroup B] [Module (𝓞 E) B]
    (ι : A ≃ₗ[𝓞 E] L) (φ : B ≃ₗ[𝓞 E] Λ) (EA : A → A → ℤ) (EB : B → B → ℤ) (f : ℕ → A →ₗ[𝓞 E] B)
    (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (ξ : E) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hJ : ∀ z : E, z ∈ J ↔ ∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (ξ * (a * z)) = m)
    (hA : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) =
      -(EA x y : ℚ))
    (hB : ∀ x y, Algebra.trace ℚ E (ξ * ∑ a, ∑ b, (φ x : Fin n → E) a * G a b * c ((φ y : Fin n → E) b)) =
      -(EB x y : ℚ))
    (h1 : ∀ N m : ℕ, 0 < N → 0 < m → ∀ a, ∃ e, f (N * m) a = f N a + N • e)
    (h2 : ∀ N : ℕ, 0 < N → (∀ a, (∃ e, f N a = N • e) ↔ ∃ e, a = N • e) ∧ ∀ a', ∃ a e, a' = f N a + N • e)
    (h3 : ∀ N : ℕ, 0 < N → ∀ a a', (N : ℤ) ∣ EB (f N a) (f N a') - EA a a') :
    ∃ g : GL (Fin n) (GlobalTheory.AdLat.RA F E),
      (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)).mulVec '' (GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) =
        GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ∧
      (∀ N : ℕ, 0 < N → ∀ a : A, ∃ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
        (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ GlobalTheory.AdLat.fv F (ι a : Fin n → E) =
          GlobalTheory.AdLat.fv F (φ (f N a) : Fin n → E) + N • w) ∧
      ∀ x y, GlobalTheory.AdLat.hermA c G ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) *ᵥ y) = GlobalTheory.AdLat.hermA c G x y := by
  let f' : ℕ → (L →ₗ[𝓞 E] Λ) := fun N => φ.toLinearMap ∘ₗ f N ∘ₗ ι.symm.toLinearMap
  have hf' : ∀ N a, f' N (ι a) = φ (f N a) := fun N a => by simp [f']
  have hlin : ∀ (s : 𝓞 E) (x y : Fin n → E), (s : E) * ∑ a, ∑ b, x a * G a b * c (y b) =
      ∑ a, ∑ b, (s • x) a * G a b * c (y b) := by
    intro s x y
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change _ = ((s : E) * x a) * _ * _
    ring
  obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.AdLat.exists_adelic_matrix_of_tower F E n L Λ f' hL hLs hΛ hΛs
    (fun N m hN hm a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      obtain ⟨e, he⟩ := h1 N m hN hm a
      exact ⟨φ e, by rw [hf', hf', he, map_add (f := _), map_nsmul]⟩)
    (fun N hN => ⟨fun a => by
      obtain ⟨a, rfl⟩ := ι.surjective a
      rw [hf']
      constructor
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).1 ⟨φ.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨ι e, by rw [he, map_nsmul]⟩
      · rintro ⟨v, hv⟩
        obtain ⟨e, he⟩ := ((h2 N hN).1 a).2 ⟨ι.symm v, by rw [← map_nsmul, ← hv, LinearEquiv.symm_apply_apply]⟩
        exact ⟨φ e, by rw [he, map_nsmul]⟩, fun a' => by
      obtain ⟨a', rfl⟩ := φ.surjective a'
      obtain ⟨a, e, he⟩ := (h2 N hN).2 a'
      exact ⟨ι a, φ e, by rw [hf', he, map_add (f := _), map_nsmul]⟩⟩)
  refine ⟨g, hg1, fun N hN a => by rw [← hf']; exact hg2 N hN (ι a), hg3 c G J ?_ ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx'⟩ := φ.surjective ⟨x, hx⟩
    obtain ⟨y', hy'⟩ := φ.surjective ⟨y, hy⟩
    rw [hJ]
    intro s
    refine ⟨-EB (s • x') y', ?_⟩
    rw [hlin, Int.cast_neg, ← hB, map_smul, hx', hy']
    rfl
  · intro N hN x y
    obtain ⟨x, rfl⟩ := ι.surjective x
    obtain ⟨y, rfl⟩ := ι.surjective y
    have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [hf', hf']
    refine ⟨(N : E)⁻¹ * ((∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) -
      ∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)), ?_, ?_⟩
    · rw [hJ]
      intro s
      obtain ⟨m, hm⟩ := h3 N hN (s • x) y
      refine ⟨-m, ?_⟩
      have e1 := hA (s • x) y
      have e2 := hB (f N (s • x)) (f N y)
      rw [map_smul, Submodule.coe_smul, ← hlin] at e1
      rw [show (φ (f N (s • x)) : Fin n → E) = s • (φ (f N x) : Fin n → E) by
        rw [map_smul, map_smul, Submodule.coe_smul], ← hlin] at e2
      have hm' : (EB (f N (s • x)) (f N y) : ℚ) - EA (s • x) y = N * m := by exact_mod_cast hm
      generalize (∑ a, ∑ b, (φ (f N x) : Fin n → E) a * G a b * c ((φ (f N y) : Fin n → E) b)) = u at e2 ⊢
      generalize (∑ a, ∑ b, (ι x : Fin n → E) a * G a b * c ((ι y : Fin n → E) b)) = v at e1 ⊢
      have e3 : ξ * ((s : E) * ((N : E)⁻¹ * (u - v))) = (N : ℚ)⁻¹ • (ξ * (s * u) - ξ * (s * v)) := by
        rw [Algebra.smul_def, map_inv₀, map_natCast]; ring
      rw [e3, map_smul, map_sub, e1, e2, smul_eq_mul]
      push_cast
      field_simp
      linear_combination -hm'
    · rw [nsmul_eq_mul, mul_inv_cancel_left₀ hN0, add_sub_cancel]

theorem onto_marking_sub (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n N : ℕ}
    {u v e : Fin n → E} {z w : Fin n → GlobalTheory.AdLat.RA F E} (h : u = v + N • e)
    (hz : z = GlobalTheory.AdLat.fv F u + N • w) : GlobalTheory.AdLat.fv F v - z = N • -(GlobalTheory.AdLat.fv F e + w) := by
  rw [hz, h, GlobalTheory.AdLat.cap_fv_add, GlobalTheory.AdLat.cap_fv_nsmul, smul_neg, smul_add]
  abel

theorem exists_finite_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  intro D H Dw l Xo c σ V r C hC k
  obtain rfl : V.rank = r := C.hr
  have hneg := (_root_.GlobalTheory.Member.exists_ctx D H Dw l Xo c σ V _ rfl C.ι hC.iota hC.pos hC.lA hC.good).2.1 C hC
  obtain ⟨Pf, -, -, hPf, -⟩ := GlobalTheory.exists_framePeriods D.host.E H Dw l Xo c σ C.g C.e C.F _ C.M hC.good hC.base hneg k
  obtain ⟨x, hx⟩ := onto_dom_nonempty (C.M.X k)
  obtain ⟨f, h1, h2, h3, h4⟩ := GlobalTheory.familyUnif_lattice_genus D.host.E H Dw l Xo _ C.g _ C.F k (Pf x) (hPf x hx)
  obtain ⟨-, hfv, -, -, -, hcc, -, -, -, hT, -⟩ := _root_.GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hL, hLs, -⟩ := _root_.GlobalTheory.Member.latG_lattice_and_completion D V 1
  let ι : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective C.ι hC.iota.emb.1).trans (LinearEquiv.ofEq _ _ hC.iota.emb.2)
  have hι : ∀ a, (ι a : Fin V.rank → D.host.E) = C.ι a := fun a => rfl
  have hherm : ∀ x y : Fin V.rank → D.host.E, (∑ a, ∑ b, x a * V.gramᵀ a b * cF D (y b)) = -herm (-V.gramᵀ) x y := by
    intro x y
    simp only [herm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hGm : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
  have hxi : (C.M.X k).ξ0 = -D.host.xi0 := (hC.modelW k).2
  obtain ⟨g, hg1, hg2, hg3⟩ := onto_adelic_of_tower D.host.F D.host.E V.rank (latG V 1) (C.M.X k).Λ hL hLs
    (C.M.X k).Λ_fg (C.M.X k).Λ_span ι (C.M.φ k) (fun a b => Dw.EF a b) (fun a b => (C.F.Di k).EF a b) f
    (cF D) V.gramᵀ D.host.xi0 _ (_root_.GlobalTheory.Member.latG_selfDual D V 1 _ rfl).1
    (fun x y => by
      have halt : Dw.EF y x = -Dw.EF x y := by
        have := Dw.alt (x + y)
        simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at this
        linear_combination this
      rw [hherm, hι, hι, ← hT, ← hC.iota.isom, halt, Int.cast_neg])
    (fun x y => by
      rw [hherm, hC.base.ef k x y, hGm, hxi, neg_neg, mul_neg, map_neg])
    h1 h2 h3
  obtain ⟨h, hh, rfl⟩ := (_root_.GlobalTheory.UnitarySplit.real_finite_split D V).2.2.2.1 g hg3
  obtain ⟨-, -, hlat, hhat, -⟩ := _root_.GlobalTheory.Member.latG_lattice_and_completion D V h
  have hcap := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank (C.M.X k).Λ (C.M.X k).Λ_fg
    (C.M.X k).Λ_span).1
  rw [hg1] at hhat
  refine ⟨h, hh, one_mem _, ?_, fun a ha => ?_⟩
  · rw [one_mul, hlat]
    ext v
    rw [SetLike.mem_coe, ← hcap, ← SetLike.mem_coe, ← hg1]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  · rw [one_mul]
    obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hw'⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    refine ⟨-(GlobalTheory.AdLat.fv D.host.F (C.M.φ k e : Fin V.rank → D.host.E) + w), ?_, ?_⟩
    · have h0 := (hcap _).2 (C.M.φ k e).2
      have h5 := AddSubgroup.neg_mem _ (AddSubgroup.add_mem _ h0 hw)
      rw [← SetLike.mem_coe, ← hhat] at h5
      exact h5
    · rw [hfv, hfv, ← hι]
      change GlobalTheory.AdLat.fv D.host.F (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      have he' : (C.M.φ k (f l.M a) : Fin V.rank → D.host.E) =
          (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) + l.M • (C.M.φ k e : Fin V.rank → D.host.E) := by
        rw [he, (C.M.φ k).map_add, map_nsmul (C.M.φ k)]
        rfl
      exact onto_marking_sub D.host.F he' hw'

end GlobalTheory.Member
end

