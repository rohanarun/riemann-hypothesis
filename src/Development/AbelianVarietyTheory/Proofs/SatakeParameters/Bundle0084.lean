module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0034
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0016
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0015
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0018
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0026
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0029
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlkDetEqDB
section
open Formalism.L2.Col

namespace GlobalTheory.TopLaw

theorem blkDet_eq_dB : ∀ {κ : Type} [CommRing κ] {n : ℕ} (β : ℕ → ℕ) (c s t : ℕ), s + t ≤ n → (∀ i, i < n → (β i = c ↔ s ≤ i ∧ i < s + t)) → ∀ (M : btG n κ β) (A : ℕ → ℕ → κ), (∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) → ((blkDet n κ β c M : κˣ) : κ) = GlobalTheory.DatumLaw.dB A s t := by
  intro κ _ n β c s t hn hβ M A hA
  rw [blkDet_val]
  unfold GlobalTheory.DatumLaw.dB
  let e : Fin t ≃ {i : Fin n // β i.1 = c} :=
    { toFun := fun u => ⟨⟨s + u.1, by have := u.2; omega⟩, (hβ _ (by have := u.2; omega)).2 ⟨by simp, by have := u.2; simp⟩⟩
      invFun := fun i => ⟨i.1.1 - s, by have := (hβ _ i.1.2).1 i.2; omega⟩
      left_inv := fun u => Fin.ext (by simp)
      right_inv := fun i => Subtype.ext (Fin.ext (by have := (hβ _ i.1.2).1 i.2; simp only; omega)) }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext u v
  exact (hA (e u).1 (e v).1).symm

end GlobalTheory.TopLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainWideTwistTransport
section
noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain

section Lattices

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  classical
  let q : V →ₗ[𝓞 K] V ⧸ W := W.mkQ.restrictScalars (𝓞 K)
  let Lb : Submodule (𝓞 K) (V ⧸ W) := L.map q
  have hfin : Module.Finite (𝓞 K) Lb := Module.Finite.iff_fg.2 (hfg.map q)
  have hcancel : ∀ (d : 𝓞 K) (x : V ⧸ W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left (by simpa using hd)
  have hflat : Module.Flat (𝓞 K) Lb := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : 𝓞 K) • (x : V ⧸ W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  have hfp : Module.FinitePresentation (𝓞 K) Lb := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 K) Lb := Module.Flat.projective_of_finitePresentation
  let qL : L →ₗ[𝓞 K] Lb := q.submoduleMap L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qL LinearMap.id (LinearMap.submoduleMap_surjective q L)
  have hs' : ∀ y : Lb, q (s y : V) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let p0 : L →ₗ[𝓞 K] V := L.subtype - L.subtype ∘ₗ s ∘ₗ qL
  have hp0 : ∀ x : L, p0 x = (x : V) - s (qL x) := fun x => rfl
  have hden : ∀ v : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
    intro v
    have hv : v ∈ Submodule.span K (L : Set V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  have hunit : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) V) x) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
    refine ⟨hunit, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let P0 : V →ₗ[𝓞 K] V := IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype p0 hunit
  have hP0 : ∀ x : L, P0 (x : V) = p0 x := fun x => IsLocalizedModule.lift_apply _ L.subtype p0 hunit x
  let P : V →ₗ[K] V := P0.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
  have hP : ∀ v, P v = P0 v := fun v => rfl
  have hW : ∀ x : L, p0 x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    change q (p0 x) = 0
    rw [hp0, map_sub, hs']
    exact sub_self _
  refine ⟨P, fun v => ?_, fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨d, hd, hv⟩ := hden v
    rw [← Submodule.Quotient.mk_eq_zero]
    apply hcancel d _ hd
    change d • q (P0 v) = 0
    rw [← map_smul, ← map_smul, show d • v = ((⟨d • v, hv⟩ : L) : V) from rfl, hP0]
    exact (Submodule.Quotient.mk_eq_zero W).2 (hW _)
  · obtain ⟨d, hd, hv⟩ := hden w
    have h0 : qL ⟨d • w, hv⟩ = 0 := by
      apply Subtype.ext
      change q (d • w) = 0
      rw [map_smul]
      change d • (Submodule.Quotient.mk w : V ⧸ W) = 0
      rw [(Submodule.Quotient.mk_eq_zero W).2 hw, smul_zero]
    have h1 : d • P0 w = d • w := by
      rw [← map_smul, show d • w = ((⟨d • w, hv⟩ : L) : V) from rfl, hP0, hp0, h0, map_zero]
      simp
    rw [hP]
    rw [← IsScalarTower.algebraMap_smul K d, ← IsScalarTower.algebraMap_smul K d w] at h1
    exact smul_right_injective V (by simpa using hd) h1
  · rw [hP, show v = ((⟨v, hv⟩ : L) : V) from rfl, hP0, hp0]
    exact L.sub_mem hv (s _).2

end Lattices


open Classical in
theorem deg_eq {ι : Type} {a b : ℕ} (e : ι × Fin b × Fin a →₀ ℕ) (τ : ι) :
    ((∑ k ∈ e.support.filter (fun k => k.1 = τ), e k : ℕ) : ℤ) = ∑ β, ∑ α, (e (τ, β, α) : ℤ) := by
  rw [← Finset.sum_product', Finset.univ_product_univ, Nat.cast_sum]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun y : Fin b × Fin a => (τ, y) ∈ e.support))]
  · refine Finset.sum_bij (fun k _ => k.2) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨h1, rfl⟩ := Finset.mem_filter.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩
    · intro k hk k' hk' h
      exact Prod.ext ((Finset.mem_filter.1 hk).2.trans (Finset.mem_filter.1 hk').2.symm) h
    · intro y hy
      exact ⟨(τ, y), Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).2, rfl⟩, rfl⟩
    · intro k hk
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hk
      rfl
  · intro y _ hy
    have : (τ, y) ∉ e.support := fun h => hy (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [show (τ, y.1, y.2) = (τ, y) from rfl, Finsupp.notMem_support_iff.1 this, Nat.cast_zero]

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Ties

variable {D : D7} {EX : ErrX D} (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))

variable (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)

end Ties

section Statements

variable (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D) (Ch : Chars (BadPrimesPeriodBound.recFields D) (BadPrimesPeriodBound.recPrimes EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) {δ : ℂ}

end Statements

end GlobalTheory.ColPeriodCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramified
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1

namespace GlobalTheory.ArtinClassCM

theorem inertia_fixes (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt)
    {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (B : ValuationSubring (Om d)) (σ : Om d ≃ₐ[KQ d] Om d) (hσ : InertiaEl B σ) :
    σ x = x := by
  obtain ⟨art, hop, hin, hfrob⟩ := hW (KQ d) (Om d)
  have hxi : IsIntegral ℤ x := by
    obtain ⟨y, hy, hyi⟩ := exists_Om d (cm1 d L hsf hd hL)
    have : y = x := Subtype.ext (hy.trans hx.symm)
    rwa [this] at hyi
  obtain ⟨P, hP, hPx⟩ := hxi
  have hxs : x ∈ fixJRoots (Ω := Om d) P := by
    rw [mem_fixJRoots hP]
    rwa [show algebraMap ℤ (Om d) = Int.castRingHom (Om d) from RingHom.ext_int _ _] at hPx
  obtain ⟨n, hn0, hn⟩ := sepInt (fixJRoots (Ω := Om d) P) (fun r hr => isIntegral_of_mem_fixJRoots hP hr)
  set S : Set (HeightOneSpectrum (𝓞 (KQ d))) := {v | (n : 𝓞 (KQ d)) ∈ v.asIdeal} with hS
  have hSfin : S.Finite := finite_places (KQ d) hn0

  have key : ∀ (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d))), LiesAbove A v → v ∉ S →
      ∀ r ∈ fixJRoots (Ω := Om d) P, ∀ r' ∈ fixJRoots (Ω := Om d) P, r - r' ∈ A.nonunits → r = r' := by
    intro A v hA hv r hr r' hr' h
    by_contra hne
    have h1 := hn r hr r' hr' hne A h
    apply hv
    rw [hS, Set.mem_ofPred_eq, ← hA]
    simpa using h1
  set H : Subgroup (Om d ≃ₐ[KQ d] Om d) := art.ker ⊓ fixJStab (KQ d) (Om d) P with hH
  have := fixJStab_normal (E := KQ d) (Ω := Om d) hP
  have hHn : H.Normal := inferInstance
  have hHo : IsOpen (H : Set (Om d ≃ₐ[KQ d] Om d)) := by
    rw [hH, Subgroup.coe_inf]
    exact hop.inter fixJStab_isOpen
  obtain ⟨A, v, φ, hA, hv, hp, hφ, hσφ⟩ := hC (KQ d) (Om d) S hSfin H hHn hHo (by
    intro A v hA hv g hg
    refine ⟨hin A g hg, fun r hr => ?_⟩
    exact key A v hA hv _ (map_mem_fixJRoots hP g hr) _ hr
      (hg.2 r (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hr)))) σ
  have hσ1 : art σ = 1 := hin B σ hσ
  have hφ1 : art φ = 1 := by
    have : σ⁻¹ * φ ∈ art.ker := hσφ.1
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ1, inv_one, one_mul] at this
    exact this
  have hcl := hfrob v A φ hA hφ
  rw [hφ1] at hcl
  have h1 := frobCong hsf hd hL x hx A v hA hp hcl.symm
  have h2 := hφ.2 x (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hxs))
  have h3 : φ x - x ∈ A.nonunits := by
    have := fixJ_nonunits_add A h2 h1
    simpa using this
  have h4 : φ x = x := key A v hA hv _ (map_mem_fixJRoots hP φ hxs) _ hxs h3
  have h5 := hσφ.2 x hxs
  rw [AlgEquiv.mul_apply, h4] at h5
  calc σ x = σ (σ⁻¹ x) := by rw [h5]
    _ = x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl

theorem good_model (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt) : CM2 := by
  refine goodReduction_of_integral_unramified jInt ?_
  intro d L hsf hd hL l _ hl hld ι
  obtain ⟨x, hx, -⟩ := exists_Om d (cm1 d L hsf hd hL)
  rw [← hx]
  exact inertKur (by omega) hld ι x fun σ hσ => inertia_fixes hW hC hsf hd hL x hx _ σ hσ

end GlobalTheory.ArtinClassCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffsWpSubst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU GlobalTheory.OnePlace Classical

namespace GlobalTheory.OnePlace

open MvPowerSeries Formalism.MainNotions.GL3Theta

theorem coeffsWp_mul {τ : Type} {p : ℕ} [Fact p.Prime] {f g : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (hg : ∀ m, coeff m g ∈ Wp p) : ∀ m, coeff m (f * g) ∈ Wp p := by
  intro m
  rw [coeff_mul]
  exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)

theorem coeffsWp_one {τ : Type} {p : ℕ} [Fact p.Prime] : ∀ m, coeff m (1 : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem coeffsWp_pow {τ : Type} {p : ℕ} [Fact p.Prime] {f : MvPowerSeries τ ℂ_[p]}
    (hf : ∀ m, coeff m f ∈ Wp p) (k : ℕ) : ∀ m, coeff m (f ^ k) ∈ Wp p := by
  induction k with
  | zero => simpa using coeffsWp_one
  | succ k ih => rw [pow_succ]; exact coeffsWp_mul ih hf

theorem coeffsWp_subst {σ τ : Type} {p : ℕ} [Fact p.Prime] {a : σ → MvPowerSeries τ ℂ_[p]} (ha : HasSubst a)
    (hA : ∀ i m, coeff m (a i) ∈ Wp p) {f : MvPowerSeries σ ℂ_[p]} (hf : ∀ m, coeff m f ∈ Wp p) :
    ∀ m, coeff m (subst a f) ∈ Wp p := by
  intro e
  rw [coeff_subst ha]
  refine finsum_induction (fun w => w ∈ Wp p) (Subring.zero_mem _) (fun x y hx hy => Subring.add_mem _ hx hy) ?_
  intro d
  refine Subring.mul_mem _ (hf d) ?_
  have hP : ∀ m, coeff m (d.prod fun s k => a s ^ k) ∈ Wp p := by
    unfold Finsupp.prod
    induction d.support using Finset.induction_on with
    | empty => simpa using coeffsWp_one
    | insert i S hi ih => rw [Finset.prod_insert hi]; exact coeffsWp_mul (coeffsWp_pow (hA i) _) ih
  exact hP e

theorem coeffsWp_X {τ : Type} {p : ℕ} [Fact p.Prime] (t : τ) : ∀ m, coeff m (X t : MvPowerSeries τ ℂ_[p]) ∈ Wp p := by
  intro m
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem hasSubst_copy {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (a : Fin r0) (b : Fin r1) :
    HasSubst (fun s : ZMod n' => (X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) := by
  have hinj : Function.Injective (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := by
    intro s t h
    simpa using h
  haveI : Filter.TendstoCofinite (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1)) := ⟨hinj.tendsto_cofinite⟩
  exact HasSubst.X_comp (fun s : ZMod n' => ((s, a, b) : ZMod n' × Fin r0 × Fin r1))

theorem xiE_props {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p])
    (hx : ∀ r, IntegralW (x r) ∧ constantCoeff (x r) = 0) (i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) :
    constantCoeff (xiE x i) = 0 ∧ ∀ m, coeff m (xiE x i) ∈ Wp p := by
  rcases i with ⟨r, a, b⟩ | ⟨r, a, b⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩
  · exact ⟨constantCoeff_subst_eq_zero (hasSubst_copy a b) (fun _ => constantCoeff_X _) (hx _).2,
      coeffsWp_subst (hasSubst_copy a b) (fun _ => coeffsWp_X _) (hx _).1⟩

theorem xiE_integral : ∀ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]), (∀ r, Formalism.MainNotions.GL3Theta.IntegralW (x r) ∧ MvPowerSeries.constantCoeff (x r) = 0) → (∀ i : Eidx n' r0 r1 ⊕ Eidx n' r0 r1, MvPowerSeries.constantCoeff (xiE x i) = 0) ∧ ∀ F : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (FormalGroupSystem.K0 p), IntS p F → ∀ m, ‖MvPowerSeries.coeff m (MvPowerSeries.subst (xiE x) (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p) F))‖ ≤ 1 := by
  intro p _ n' r0 r1 x hx
  have hP := xiE_props (r0 := r0) (r1 := r1) x hx
  refine ⟨fun i => (hP i).1, ?_⟩
  intro F hF m
  obtain ⟨g, rfl⟩ := hF
  have hs : HasSubst (xiE x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → _) :=
    hasSubst_of_constantCoeff_zero fun i => (hP i).1
  have hG : ∀ d, coeff d (MvPowerSeries.map (Formalism.L2.G.Pend.k0ToC p)
      (MvPowerSeries.map (algebraMap (FormalGroupSystem.WW p) (FormalGroupSystem.K0 p)) g)) ∈ Wp p := by
    intro d
    rw [coeff_map, coeff_map]
    rw [Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
    exact Formalism.L2.G.Pend.wToC_mem_Wp p _
  exact GlobalTheory.BeProps.norm_le_one_of_mem_Wp (coeffsWp_subst hs (fun i => (hP i).2) hG m)

end GlobalTheory.OnePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
section
noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

section Alg

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

theorem charpoly_smul [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem twGL_val {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (W : Submodule K (Fin a → K)) :
    IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
    rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem ss_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := fun W hW => by
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL ρ χ W').2 hW', hc⟩

end Alg

theorem ms_one {s : Multiset ℕ} (h : s.sum = 1) (h1 : ∀ a ∈ s, 1 ≤ a) : s = {1} := by
  have hne : s ≠ 0 := by rintro rfl; simp at h
  have hc := Multiset.card_nsmul_le_sum h1
  have hp := Multiset.card_pos.2 hne
  rw [smul_eq_mul, mul_one, h] at hc
  have hc1 : Multiset.card s = 1 := by omega
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hc1
  simp only [Multiset.sum_singleton] at h
  rw [h]

theorem sum_split {M : Type} [AddCommMonoid M] {n m : ℕ} (h : n = m + 1) (f : Fin n → M) :
    ∑ k, f k = ∑ k : Fin m, f (Fin.cast h.symm k.castSucc) + f (Fin.cast h.symm (Fin.last m)) := by
  subst h
  simp [Fin.sum_univ_castSucc]

theorem prod_flatMap' {α M : Type} [CommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_flat {M : Type} [CommMonoid M] (n : ℕ) (d : Fin n → ℕ) (f : Fin n → ℕ → M) :
    (((List.finRange n).map fun k => ((List.range (d k)).map (f k)).prod)).prod =
      ∏ k, ∏ a ∈ Finset.range (d k), f k a := by
  rw [Fin.prod_univ_def]
  congr 1

variable (D : D7) (i : D.nd.Loc)

def eU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)

def cU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (D.nd.chi i 1)

theorem eU_pow (g : G D.host.E D.nd.Om) (a : ℕ) :
    ((((eU D i)⁻¹ ^ a) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) = (epsQ D i g)⁻¹ ^ a := by
  rw [MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rfl

def twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) :
    List (Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))) :=
  (List.finRange Pa.length).flatMap fun k =>
    (List.range (Pa.get k).d).map fun a => ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩

theorem mem_twList {Pa : List (Part D.naut.CG)}
    {R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))}
    {p : Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))} (hp : p ∈ twList D i Pa R) :
    ∃ k : Fin Pa.length, ∃ a < (Pa.get k).d,
      p = ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
  exact ⟨k, a, List.mem_range.1 ha, rfl⟩

theorem twList_cp (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (g : G D.host.E D.nd.Om) :
    ((twList D i Pa R).map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) (Qbar (D.nd.l i))).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
          ((epsQ D i g)⁻¹ ^ a) := by
  rw [twList, List.map_flatMap, prod_flatMap']
  simp only [List.map_map, Function.comp_def]
  rw [prod_flat]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun a _ => ?_
  rw [twGL_val, charpoly_smul _ (Units.ne_zero _), eU_pow]

theorem mapRep_val {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).map f := rfl

theorem eig_map (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)) (v : Fin D.R.nV → Kf D.nd i)
    (hv0 : v ≠ 0) (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    ∃ w : Fin D.R.nV → Qbar (D.nd.l i), w ≠ 0 ∧ ∀ g,
      ((mapRep (iotaOQ D.nd D.naut i) r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).mulVec w =
        ((cU D i g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) • w := by
  refine ⟨fun j => D.naut.iotaQ i (v j), fun h => hv0 (funext fun j => ?_), fun g => funext fun j => ?_⟩
  · have := congrFun h j
    exact (D.naut.iotaQ i).injective (by simpa using this)
  · have e1 := congrArg (D.naut.iotaQ i) (congrFun (hv g) j)
    rw [RingHom.map_mulVec, mapRep_val] at e1
    rw [mapRep_val]
    refine e1.trans ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul]
    rfl

end GlobalTheory.EigenPoint
end
end

