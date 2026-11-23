module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024

@[expose] public section
set_option maxHeartbeats 8000000

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegular
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem chartSub_div_mem {F : Type} [Field F] {κ : Type} (x : κ → F) (c j : κ) :
    x j / x c ∈ chartSub x c :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem chartSub_le_of_forall {F : Type} [Field F] {κ : Type} {x : κ → F} {c : κ} {T : Subring F}
    (h : ∀ j, x j / x c ∈ T) : chartSub x c ≤ T := by
  intro a ha
  have ha' : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := ha
  induction ha' using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    exact h j
  | algebraMap n => simpa using intCast_mem T n
  | add b d _ _ hb hd => exact T.add_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))
  | mul b d _ _ hb hd => exact T.mul_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))

theorem locSub_le_of {F : Type} [Field F] {R T : Subring F} {a : F} (h : R ≤ T) (ha : a⁻¹ ∈ T) :
    locSub R a ≤ T :=
  Subring.closure_le.2 (Set.union_subset h (Set.singleton_subset_iff.2 ha))

theorem flagCoord_div_eq {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type}
    (x : κ → Ω) {S : Type} [Fintype S] {r n m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω}
    {c₀ : κ} (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (hx : x c₀ ≠ 0)
    (h : ∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) (k : κ)
    (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc ((k, J') : FlagIx κ n r) / flagCoord κ x φ cc ((c₀, J) : FlagIx κ n r) =
      algebraMap Ω (GenField Ω r) (x k / x c₀) *
        ∏ q : (Σ s, Fin (r s)), stepMinor (flagB M T q.1) q.2 (J' q) / stepMinor (flagB M T q.1) q.2 (J q) := by
  have hi : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := (map_ne_zero _).2 hx
  rw [flagCoord_eq x h k J', flagCoord_eq x h c₀ J, map_div₀, mul_div_mul_comm,
    ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hi))

theorem chartRing_eq_ratioRing : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type)
    (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω)
    (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 →
    g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) →
    (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) →
    algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧
    locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) =
      ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  intro Ω _ E _ _ κ x S _ r n m φ cc M T c₀ J g hx hg hg0 h hJ
  classical
  set A := chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) with hA
  have hdiv := fun k J' => flagCoord_div_eq (m := m) x J hx h k J'

  have h1 : ∀ k, algebraMap Ω (GenField Ω r) (x k / x c₀) ∈ A := by
    intro k
    have e := hdiv k J
    have e1 : ∏ q : (Σ s, Fin (r s)),
        stepMinor (flagB M T q.1) q.2 (J q) / stepMinor (flagB M T q.1) q.2 (J q) = 1 :=
      Finset.prod_eq_one fun q _ => div_self (hJ q)
    rw [e1, _root_.mul_one] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ((k, J) : FlagIx κ n r)

  have h2 : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A := by
    intro q J'
    have e := hdiv c₀ (Function.update J q J')
    rw [div_self hx, map_one, _root_.one_mul, Finset.prod_div_distrib,
      prod_update_div (β := fun q : (Σ s, Fin (r s)) => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => stepMinor (flagB M T q.1) q.2 b) J hJ q J'] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)
      ((c₀, Function.update J q J') : FlagIx κ n r)
  have himg : chartSub x c₀ ≤ A.comap (algebraMap Ω (GenField Ω r)) :=
    chartSub_le_of_forall fun j => h1 j
  have hgA : algebraMap Ω (GenField Ω r) g ∈ A := himg hg
  refine ⟨hgA, le_antisymm ?_ ?_⟩
  ·
    set R' := locSub (chartSub x c₀) g with hR'
    have him : ∀ b ∈ R', algebraMap Ω (GenField Ω r) b ∈ ratioRing R' (flagB M T) J := fun b hb =>
      Subring.subset_closure (Or.inl ⟨b, hb, rfl⟩)
    refine locSub_le_of (chartSub_le_of_forall ?_) ?_
    · rintro ⟨k, J'⟩
      rw [hdiv k J']
      refine Subring.mul_mem _ (him _ (le_locSub _ _ (chartSub_div_mem x c₀ k))) ?_
      exact Subring.prod_mem _ fun q _ => Subring.subset_closure (Or.inr ⟨q, J' q, rfl⟩)
    · rw [← map_inv₀]
      exact him _ (inv_mem_locSub _ _)
  · refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨b, hb, rfl⟩
      have hle : locSub (chartSub x c₀) g ≤
          (locSub A (algebraMap Ω (GenField Ω r) g)).comap (algebraMap Ω (GenField Ω r)) := by
        refine locSub_le_of (himg.trans fun a ha => le_locSub _ _ ha) ?_
        show algebraMap Ω (GenField Ω r) g⁻¹ ∈ locSub A (algebraMap Ω (GenField Ω r) g)
        rw [map_inv₀]
        exact inv_mem_locSub _ _
      exact hle hb
    · rintro _ ⟨q, J', rfl⟩
      exact le_locSub _ _ (h2 q J')

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePoint
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chart_prime_point : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ), x c ≠ 0 → ∀ P : Ideal (chRing o x c), P.IsPrime → ∃! p : Cpt M.ξ, InChart M.ξ x c p ∧ ∀ u : chRing o x c, u ∈ P ↔ ¬ unitAt M.ξ p (u : Ω) :=
  @PositivityTheory.HtPt.Ma.prime_pt

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartUnitBasicOpen
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chRing_basicOpen_basis : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ) (U : M.X.Opens), InChart M.ξ x c p → p.1 ∈ U → ∃ f ∈ chRing o x c, unitAt M.ξ p f ∧ ∀ q : Cpt M.ξ, InChart M.ξ x c q → unitAt M.ξ q f → q.1 ∈ U :=
  @PositivityTheory.HtPt.Ma.basic

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosure
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem coh_vb_images_sums_multiples : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (L L' : Lat ξ E) (T : Set (Cpt ξ)), (∀ r V, L.IsVBOn T r V → L.IsCohOn T) ∧ (∀ φ : E →ₗ[Ω] E', L.IsCohOn T → (L.map φ).IsCohOn T) ∧ (L.IsCohOn T → L'.IsCohOn T → Lat.IsCohOn (fun p => L p ⊔ L' p : Lat ξ E) T) ∧ (∀ (r : ℕ) (V : Submodule Ω E) (a : Ω), a ≠ 0 → L.IsVBOn T r V → (L.scale a).IsVBOn T r V) ∧ (∀ (r : ℕ) (V : Submodule Ω E), L.IsCohOn T → (∀ p ∈ T, ∃ b : Fin r → E, Submodule.span Ω (Set.range b) = V ∧ L.IsFrameAt b p) → L.IsVBOn T r V) :=
  @PositivityTheory.HtPt.Mc.coh_ops

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbeddingStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_point_existsUnique_embedding : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω), OverInt y φ → ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver | exact GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_ptOver <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantSmoothMapCoords
section
noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartSmooth

open GlobalTheory.CompanionTheory.Ar.ChartFin

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem mem_adjoin_iff {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) (a : Ω) :
    a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s : Γ(X, U), secVal ξ U h s = a := by
  rw [T.ring c hc a]
  constructor
  · intro H
    refine exists_secVal hall T.gen.inj U h a fun q hq => ?_
    obtain ⟨h', hi⟩ := (hU q).1 hq
    exact H _ hi
  · rintro ⟨s, rfl⟩ p hp
    have hq : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
    exact ⟨_, _root_.GlobalTheory.CompanionTheory.Ar.ChartFin.genMap_germ ξ h hq p.2 s⟩

theorem exists_secEquiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) :
    ∃ E : Γ(X, U) ≃+* Algebra.adjoin o (Set.range fun j => x j / x c),
      ∀ s, ((E s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = secVal ξ U h s := by
  have hm : ∀ s, secVal ξ U h s ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun s =>
    (mem_adjoin_iff hall T hc hU h _).2 ⟨s, rfl⟩
  refine ⟨RingEquiv.ofBijective ((secVal ξ U h).codRestrict _ hm) ⟨fun a b e => ?_, fun r => ?_⟩, fun _ => rfl⟩
  · exact secVal_injective hall T.gen.inj U h (congrArg Subtype.val e)
  · obtain ⟨s, hs⟩ := (mem_adjoin_iff hall T hc hU h r).1 r.2
    exact ⟨s, Subtype.ext hs⟩

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

theorem inChart_map {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} {κ κ' : Type} {x : κ → Ω} {x' : κ' → Ω'} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (T' : CoordTie ℤ ξ' x') (hd : Dominates ξ' ξ f i) {c : κ} {c' : κ'} (hc : x c ≠ 0)
    (hc' : x' c' ≠ 0) (hi : ∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'))
    (p' : Cpt ξ') (hp' : InChart ξ' x' c' p') : InChart ξ x c ⟨f p'.1, hall _⟩ := by
  obtain ⟨h, hreg, hunit⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  obtain ⟨d, hd0, hdr⟩ := T.cover ⟨f p'.1, h⟩
  have ha0 : x c / x d ≠ 0 := div_ne_zero hc hd0
  have hinv : (i (x c / x d))⁻¹ ∈ regAt ξ' p' := by
    rw [← map_inv₀, inv_div]
    exact (T'.ring c' hc' _).1 (hi d) p' hp'
  have hu := hunit T'.gen _ (hdr c) ⟨(map_ne_zero i).2 ha0, hreg _ (hdr c), hinv⟩
  refine ⟨hc, fun j => ?_⟩
  have e : x j / x c = x j / x d * (x c / x d)⁻¹ := by
    field_simp
  rw [e]
  exact mul_mem (hdr j) hu.2.2

theorem smooth_chartRing (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω) :
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  intro hall hall' T T' hd hsm c c' hc hc' hi
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  obtain ⟨U', hU'a, hU'm⟩ := T'.affine c' hc'
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  have hg' : genPt ξ' ∈ U' := (hU'm _).2 ⟨specializes_rfl, inChart_genPt T'.gen hc'⟩
  have hle : U' ≤ f ⁻¹ᵁ U := by
    intro q hq
    obtain ⟨h, hin⟩ := (hU'm q).1 hq
    exact (hUm (f q)).2 ⟨hall _, inChart_map hall T T' hd hc hc' hi ⟨q, h⟩ hin⟩
  obtain ⟨E, hE⟩ := exists_secEquiv hall T hc hUm hg
  obtain ⟨E', hE'⟩ := exists_secEquiv hall' T' hc' hU'm hg'
  have hs : (f.appLE U U' hle).hom.Smooth := Smooth.smooth_appLE (f := f) hUa hU'a hle
  have hval : ∀ s, secVal ξ' U' hg' ((f.appLE U U' hle).hom s) = i (secVal ξ U hg s) := by
    intro s
    have h2 : genPt ξ' ∈ f ⁻¹ᵁ U := hle hg'
    rw [← secVal_app hd U hg h2 s, ← secVal_res ξ' (homOfLE hle) hg' h2 ((f.app U).hom s)]
    rfl
  refine ⟨(E'.toRingHom.comp (f.appLE U U' hle).hom).comp E.symm.toRingHom, fun a => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective a
    simp only [RingHom.comp_apply]
    have : E.symm.toRingHom (E s) = s := E.symm_apply_apply s
    rw [this]
    exact (hE' _).trans ((hval s).trans (congrArg i (hE s).symm))
  · have hr := RingHom.Smooth.propertyIsLocal.respectsIso
    exact hr.2 _ E.symm (hr.1 _ E' hs)

end GlobalTheory.CompanionTheory.Ar.ChartSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesRegAtLocal
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem dominates_localRings : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (f : X' ⟶ X), Dominates ξ' ξ f i → ∀ p' : Cpt ξ', ∃ h : genPt ξ ⤳ f p'.1, ((∀ a ∈ regAt ξ ⟨f p'.1, h⟩, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt ξ ⟨f p'.1, h⟩, unitAt ξ' p' (i a) → unitAt ξ ⟨f p'.1, h⟩ a) :=
  PositivityTheory.HtPt.Mb.dom_local

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompatStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_model_chart_compat : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ'), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') → (∀ c, x c ≠ 0 → y (e c) ≠ 0) → (∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p) → (∀ c, x c ≠ 0 → ∃ s : Finset Ω', ∀ a : Ω', a ∈ chRing o y (e c) ↔ a ∈ Submodule.span (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (s : Set Ω')) → IsFinite f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts | exact GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmooth
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem val_appLE_of_dominates {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
    (hd : Dominates ξ' ξ f i) {U : X.Opens} {W : X'.Opens} (e : W ≤ f ⁻¹ᵁ U) (hW : genPt ξ' ∈ W)
    (hU : genPt ξ ∈ U) (t : Γ(X, U)) :
    (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) =
      i ((X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t) := by
  have hfq : f (genPt ξ') ∈ U := e hW
  have hp : genPt ξ ⤳ f (genPt ξ') := by rw [RegAtDom.map_genPt hd]
  have h := RegAtDom.genMap_stalkMap hd (genPt ξ') specializes_rfl hp
    ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t)
  have l1 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ f.stalkMap (genPt ξ') =
      f.appLE U W e ≫ X'.presheaf.germ W (genPt ξ') hW := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have l2 : X'.presheaf.germ W (genPt ξ') hW ≫ X'.presheaf.stalkSpecializes specializes_rfl =
      X'.presheaf.germ W (genPt ξ') hW := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have l3 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ X.presheaf.stalkSpecializes hp =
      X.presheaf.germ U (genPt ξ) hU := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have a1 : (f.stalkMap (genPt ξ')).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t) :=
    congrArg (fun g => g.hom t) l1
  have a2 : ∀ s, (X'.presheaf.stalkSpecializes specializes_rfl).hom
      ((X'.presheaf.germ W (genPt ξ') hW).hom s) = (X'.presheaf.germ W (genPt ξ') hW).hom s :=
    fun s => congrArg (fun g => g.hom s) l2
  have a3 : (X.presheaf.stalkSpecializes hp).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU).hom t := congrArg (fun g => g.hom t) l3
  rw [a1] at h
  have b1 : genMap ξ' ⟨genPt ξ', specializes_rfl⟩ ((X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t)) =
      (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) := by
    exact congrArg (Scheme.stalkClosedPointTo ξ').hom (a2 _)
  have b2 : genMap ξ ⟨f (genPt ξ'), hp⟩ ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t := by
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom a3
  rw [← b1, h, b2]

theorem smooth_of_pieces : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i →
    (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C),
      IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧
      ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hg hg' hd h
  refine (HasRingHomProperty.iff_exists_appLE (P := @Smooth) (Q := RingHom.Smooth)
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1).2 fun p' => ?_
  obtain ⟨U, W, R, C, hRC, hU, hW, e, hp, hs⟩ := h p'
  refine ⟨⟨U, hU.affine⟩, ⟨W, hW.affine⟩, hp, e, ?_⟩
  have hWg : genPt ξ' ∈ W := (hW.spec p' hp).mem_open W.isOpen hp
  have hUg : genPt ξ ∈ U := by
    have h1 : f (genPt ξ') ∈ U := e hWg
    rwa [RegAtDom.map_genPt hd] at h1
  obtain ⟨injU, ranU⟩ := _root_.GlobalTheory.CompanionTheory.Ar.regAt_sections X Ω ξ hg U hUg hU.spec
  obtain ⟨injW, ranW⟩ := _root_.GlobalTheory.CompanionTheory.Ar.regAt_sections X' Ω' ξ' hg' W hWg hW.spec
  have memR : ∀ t, (X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom t ∈ R :=
    fun t => (hU.ring _).2 ((ranU _).1 ⟨t, rfl⟩)
  have memC : ∀ t, (X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom t ∈ C :=
    fun t => (hW.ring _).2 ((ranW _).1 ⟨t, rfl⟩)
  let eU : Γ(X, U) ≃+* R := RingEquiv.ofBijective
    ((X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom.codRestrict R memR)
    ⟨fun a b hab => injU (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranU r.1).2 ((hU.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  let eW : Γ(X', W) ≃+* C := RingEquiv.ofBijective
    ((X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom.codRestrict C memC)
    ⟨fun a b hab => injW (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranW r.1).2 ((hW.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  have hval : ∀ t, eW ((f.appLE U W e).hom t) =
      ((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)) (eU t) :=
    fun t => Subtype.ext (val_appLE_of_dominates hd e hWg hUg t)
  have key : (f.appLE U W e).hom = (eW.symm : C →+* Γ(X', W)).comp
      (((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)).comp (eU : Γ(X, U) →+* R)) :=
    RingHom.ext fun t => (eW.symm_apply_eq.2 (hval t).symm).symm
  show RingHom.Smooth (f.appLE U W e).hom
  rw [key]
  exact RingHom.Smooth.comp (RingHom.Smooth.comp (RingHom.Smooth.of_bijective eU.bijective) hs)
    (RingHom.Smooth.of_bijective eW.symm.bijective)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsComplexPointNonvanishing
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_ptOver_ne : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (g : MRing ι) (d : K → ℕ), OverInt y φ → IsMultiHomog g d → g ∉ mCoordIdeal y → ∃ z, PtOver y φ σ z ∧ evC z g ≠ 0 :=
  @PositivityTheory.Xgn.exists_point_over_nonvanishing

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueHostAutEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HostAutTrans

theorem existsUnique_hostAut_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [IsGalois ℚ E] (τ τ' : E →+* ℂ), τ (H.rt : E) = H.rt0 → τ' (H.rt : E) = H.rt0 → ∃! g : HostAut H, τ' = τ.comp g.σ.toRingHom := by
  intro E _ _ _ H _ τ τ' hτ hτ'
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ τ'
    (Subsingleton.elim _ _)
  have key : ∀ x, τ' x = τ (σ.symm x) := fun x => by rw [← hσ]; rfl
  refine ⟨⟨σ.symm.toRingEquiv, τ.injective ((key _).symm.trans (hτ'.trans hτ.symm))⟩, ?_, ?_⟩
  · exact RingHom.ext fun x => key x
  · rintro ⟨g₀, hfix⟩ hg
    have hx : ∀ x, g₀ x = σ.symm x := fun x =>
      τ.injective ((RingHom.congr_fun hg x).symm.trans (key x))
    have h0 : g₀ = σ.symm.toRingEquiv := RingEquiv.ext fun x => hx x
    subst h0
    rfl

end GlobalTheory.CompanionTheory.Ar.HostAutTrans
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatiosStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_chart_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S] (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → (∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) → ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | exact GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate <;> assumption)
end

