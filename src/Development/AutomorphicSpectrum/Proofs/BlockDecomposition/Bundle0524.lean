module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroup
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open _root_.Topology

theorem exists_den {F : Type} [Field F] [NumberField F] (y : F) :
    ∃ D : ℕ, 0 < D ∧ ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y := by
  have hal : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨z, hz, hint⟩ := hal.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_⟩
  have hint' : IsIntegral ℤ ((z.natAbs : F) * y) := by
    rcases Int.natAbs_eq z with h | h
    · have : ((z.natAbs : F) * y) = z • y := by
        rw [zsmul_eq_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rwa [this]
    · have : ((z.natAbs : F) * y) = -(z • y) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rw [this]
      exact hint.neg
  exact ⟨IsIntegralClosure.mk' (𝓞 F) _ hint', IsIntegralClosure.algebraMap_mk' _ _ _⟩

theorem exists_common_den {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (y : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y i := by
  choose D hD r hr using fun i => exists_den (y i)
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(m : 𝓞 F) * r i, ?_⟩
  rw [hm, map_mul, hr, map_natCast]
  push_cast
  ring

theorem coords_den {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (o : 𝓞 E) (k : Fin d), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = (D : F) * b.repr (algebraMap (𝓞 E) E o) k := by
  let e := RingOfIntegers.basis E
  obtain ⟨D, hD, h⟩ := exists_common_den (F := F)
    (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d => b.repr (algebraMap (𝓞 E) E (e p.1)) p.2)
  refine ⟨D, hD, fun o k => ?_⟩
  choose r hr using h
  refine ⟨∑ i, (e.repr o i) • r (i, k), ?_⟩
  have ho : algebraMap (𝓞 E) E o = ∑ i, (e.repr o i) • algebraMap (𝓞 E) E (e i) := by
    conv_lhs => rw [← e.sum_repr o]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ho, map_sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, hr (i, k)]
  simp only [zsmul_eq_mul]
  ring

theorem nhds_unif {ι Y : Type} [Finite ι] [TopologicalSpace Y] (y0 : Y) (W : Set (ι → Y))
    (hW : W ∈ 𝓝 (fun _ => y0)) : ∃ V ∈ 𝓝 y0, ∀ y : ι → Y, (∀ i, y i ∈ V) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr ht, fun y hy => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hy i) i

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open _root_.Topology

theorem exists_smul_mem_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  intro F E _ _ _ _ _ σ hcm n U hU t ht
  obtain ⟨-, hSC, hT2, -, -, -, hF, hN, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  haveI : SecondCountableTopology (Af F) := hSC
  haveI : T2Space (Af F) := hT2
  haveI : LocallyCompactSpace (Af F) := (_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).1
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Af F)
  let b := Module.finBasis F E
  have hh := hH _ b
  set h := hh.homeomorph with hdef
  have happ : ∀ (y : Af F ⊗[F] E) k, h y k = (Algebra.TensorProduct.basis (Af F) b).repr y k :=
    fun _ _ => rfl
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hU
  let G : (Fin n × Fin n × Fin (Module.finrank F E) → Af F) →
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun x a c => h.symm (fun k => x (a, c, k))
  have hG : Continuous G := by
    refine continuous_matrix fun a c => ?_
    exact h.symm.continuous.comp (continuous_pi fun k => continuous_apply _)
  have hG0 : G (fun _ => 0) = 0 := by
    ext a c
    apply h.injective
    show h (h.symm _) = h 0
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    simp
  have h0 : (0 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ U' := by
    have h1 : (0 : HermR (Af F) σ n) ∈ (U : Set (HermR (Af F) σ n)) := U.zero_mem
    rw [← hU'] at h1
    exact h1
  have hW : G ⁻¹' U' ∈ 𝓝 (fun _ => (0 : Af F)) :=
    (hU'o.preimage hG).mem_nhds (by rw [Set.mem_preimage, hG0]; exact h0)
  obtain ⟨V, hV, hVW⟩ := nhds_unif _ _ hW
  obtain ⟨N, hNpos, hNV⟩ := hN V hV
  obtain ⟨D₁, hD₁, p, hp⟩ := exists_den (t⁻¹)
  obtain ⟨D₂, hD₂, hco⟩ := coords_den b
  refine ⟨D₁ * D₂ * N, by positivity, fun c hc => ?_⟩
  let y : Fin n × Fin n × Fin (Module.finrank F E) → Af F := fun q =>
    algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 q.1 q.2.1) q.2.2)
  have hy : ∀ q, y q ∈ V := by
    rintro ⟨a, a', k⟩
    obtain ⟨o, ho⟩ := hc a a'
    obtain ⟨r, hr⟩ := hco o k
    have hval : b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k
        = (N : F) * (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) := by
      have : (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a')
          = (((D₁ * D₂ * N : ℕ) : F) / t) • algebraMap (𝓞 E) E o := by
        rw [ho]; rfl
      rw [this, map_smul, Finsupp.smul_apply, hp, hr, smul_eq_mul, div_eq_mul_inv]
      push_cast
      ring
    have hmem : algebraMap F (Af F) (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) ∈
        GlobalTheory.CompanionTheory.SW.Core.Oh F := (hF _).mpr ⟨p * r, by simp⟩
    have := hNV _ hmem
    show algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k) ∈ V
    rw [hval, map_mul, map_natCast]
    exact this
  have hGy : G y ∈ U' := hVW y hy
  have heq : G y = (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 := by
    ext a a'
    apply h.injective
    show h (h.symm _) = _
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    show y (a, a', k) = _
    have hentry : (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 a a' =
        (1 : Af F) ⊗ₜ[F] (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') := rfl
    rw [hentry, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, one_smul, Finsupp.mapRange_apply]
    rfl
  have hfin : hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c) ∈ (U : Set (HermR (Af F) σ n)) := by
    rw [← hU']
    show _ ∈ U'
    rw [← heq]
    exact hGy
  exact hfin

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecomposition
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.DecN

open NumberField IsDedekindDomain GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec
open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport
open scoped _root_.Topology

variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def lvN (v : HeightOneSpectrum (𝓞 F)) (P : AddSubgroup (Fv F v)) (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → Fv F v ⊗[F] E) where
  carrier := {Z | ∀ a i k, crd b (Fv F v) (Z a i) k ∈ P}
  add_mem' hx hy a i k := by
    rw [Pi.add_apply, Pi.add_apply, crd_add]
    exact add_mem (hx a i k) (hy a i k)
  zero_mem' a i k := by
    rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
    exact zero_mem P
  neg_mem' hx a i k := by
    rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
    exact neg_mem (hx a i k)

theorem isClopen_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (n M : ℕ) :
    IsClopen (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  have hc : ∀ (x : Fin n) (i : Fin M) (k : Fin d),
      Continuous (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) :=
    fun x i k => (continuous_crd b (Fv F v) k).comp ((continuous_apply i).comp (continuous_apply x))
  have e : (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) = ⋂ x, ⋂ i, ⋂ k,
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Y x i) k) ⁻¹' (P : Set (Fv F v)) := by
    ext Y
    simp [lvN]
  rw [e]
  exact ⟨isClosed_iInter fun x => isClosed_iInter fun i => isClosed_iInter fun k =>
    P.isClosed.preimage (hc x i k), isOpen_iInter_of_finite fun x =>
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => P.isOpen.preimage (hc x i k)⟩

theorem isCompact_lvN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v) (n M : ℕ) :
    IsCompact (lvN b v (P : AddSubgroup (Fv F v)) n M : Set (Fin n → Fin M → Fv F v ⊗[F] E)) :=
  (isCompact_latV b v n M).of_isClosed_subset (isClopen_lvN b v P n M).isClosed
    fun _ hZ a i k => hP (hZ a i k)

theorem projV_subN (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X - Y) = projV v X - projV v Y := by
  funext a i
  simp [projV, map_sub]

def cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) {n M : ℕ}
    (a : Fin n → Fin M → Fv F v ⊗[F] E) : Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
  {Z | Z - a ∈ lvN b v (P : AddSubgroup (Fv F v)) n M}

theorem isCompact_isOpen_cosVN (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) (hP : P ≤ intSub v)
    {n M : ℕ} (a : Fin n → Fin M → Fv F v ⊗[F] E) : IsCompact (cosVN b v P a) ∧ IsOpen (cosVN b v P a) := by
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have e : cosVN b v P a = (Homeomorph.subRight a) ⁻¹' (lvN b v (P : AddSubgroup (Fv F v)) n M : Set _) := rfl
  rw [e]
  exact ⟨(Homeomorph.subRight a).isCompact_preimage.2 (isCompact_lvN b v P hP n M),
    (isClopen_lvN b v P n M).isOpen.preimage (Homeomorph.subRight a).continuous⟩

theorem cosVN_intSub (v : HeightOneSpectrum (𝓞 F)) {n M : ℕ} {a : Fin n → Fin M → Fv F v ⊗[F] E}
    (ha : a ∈ latV b v) : cosVN b v (intSub v) a = latV b v := by
  have ha' : a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := ha
  ext Z
  have e1 : Z ∈ cosVN b v (intSub v) a ↔ Z - a ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M :=
    Iff.rfl
  have e2 : Z ∈ latV b v ↔ Z ∈ lvN b v ((intSub v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M := Iff.rfl
  rw [e1, e2, sub_eq_add_neg]
  exact add_mem_cancel_right (neg_mem ha')

theorem exists_box_combN {n M : ℕ} (g : (Fin n → Fin M → Af F ⊗[F] E) → ℂ) (hg : IsSB g) :
    ∃ (s : Finset (Fin n → Fin M → Af F ⊗[F] E))
      (A : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
      (S : Finset (HeightOneSpectrum (𝓞 F))),
      (∀ a v, IsCompact (A a v) ∧ IsOpen (A a v)) ∧ (∀ a ∈ s, ∀ v, v ∉ S → A a v = latV b v) ∧
        ∀ Y, g Y = ∑ a ∈ s, g a * (boxF (A a)).indicator (fun _ => (1 : ℂ)) Y := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have hU := invariant_mem_nhds hg.1 hg.2
  let Lc : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous Lc := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  have hL0 : Lc (fun _ _ _ => 0) = 0 := by
    funext x i
    simp [Lc]
  have hp : Lc ⁻¹' {u | ∀ x, g (x + u) = g x} ∈ 𝓝 (fun _ => fun _ => fun _ => (0 : Af F)) :=
    hL.continuousAt.preimage_mem_nhds (by rw [hL0]; exact hU)
  obtain ⟨W1, hW1, h1⟩ := exists_nhds_of_pi hp
  obtain ⟨W2, hW2, h2⟩ := exists_nhds_of_pi hW1
  obtain ⟨W, hW, h3⟩ := exists_nhds_of_pi hW2
  obtain ⟨T, P, hPO, hPT, hsub⟩ := exists_box_subset hW
  let B : AddSubgroup (Af F) :=
    { carrier := {y | ∀ v, y v ∈ P v}
      add_mem' := fun hx hy v => add_mem (hx v) (hy v)
      zero_mem' := fun v => zero_mem (P v)
      neg_mem' := fun hx v => neg_mem (hx v) }
  have hBo : IsOpen (B : Set (Af F)) := by
    have e : (B : Set (Af F)) = {y : Af F | ∀ v, y v ∈ v.adicCompletionIntegers F} ∩
        ⋂ v ∈ T, (fun y : Af F => y v) ⁻¹' (P v : Set (Fv F v)) := by
      ext y
      constructor
      · intro hy
        exact ⟨fun v => hPO v (hy v), Set.mem_iInter₂.2 fun v _ => hy v⟩
      · rintro ⟨hy1, hy2⟩ v
        by_cases hv : v ∈ T
        · exact Set.mem_iInter₂.1 hy2 v hv
        · rw [hPT v hv]
          exact hy1 v
    rw [e]
    refine IsOpen.inter ?_ (T.finite_toSet.isOpen_biInter fun v _ => (P v).isOpen.preimage
      (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v))
    exact RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  let L : AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) :=
    { carrier := {X | ∀ a i k, crd b (Af F) (X a i) k ∈ B}
      add_mem' := fun {x y} hx hy a i k => by
        rw [Pi.add_apply, Pi.add_apply, crd_add]
        exact add_mem (hx a i k) (hy a i k)
      zero_mem' := fun a i k => by
        rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
        exact zero_mem B
      neg_mem' := fun {x} hx a i k => by
        rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
        exact neg_mem (hx a i k) }
  have hLo : IsOpen (L : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
    have e : (L : Set (Fin n → Fin M → Af F ⊗[F] E)) = ⋂ a, ⋂ i, ⋂ k,
        (fun X : Fin n → Fin M → Af F ⊗[F] E => crd b (Af F) (X a i) k) ⁻¹' (B : Set (Af F)) := by
      ext X
      simp [L]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      hBo.preimage ((continuous_crd b (Af F) k).comp ((continuous_apply i).comp (continuous_apply a)))
  have hinv : ∀ x, ∀ l ∈ L, g (x + l) = g x := by
    intro x l hl
    have hl' : l = Lc fun a i k => crd b (Af F) (l a i) k := by
      funext a i
      exact eq_sum_crd b (Af F) (l a i)
    rw [hl']
    refine h1 _ (fun a => h2 _ fun i => h3 _ fun k => hsub (hl a i k)) x
  obtain ⟨s, hs⟩ := eq_sum_cosets hg.2 L hLo hinv
  have hbad : ∀ a : Fin n → Fin M → Af F ⊗[F] E, {v | ¬ projV v a ∈ latV b v}.Finite := fun a =>
    Filter.eventually_cofinite.1 (eventually_mem_latV b a)
  refine ⟨s, fun a v => cosVN b v (P v) (projV v a), T ∪ s.biUnion fun a => (hbad a).toFinset,
    fun a v => isCompact_isOpen_cosVN b v (P v) (hPO v) _, fun a ha v hv => ?_, fun Y => ?_⟩
  · have hvT : v ∉ T := fun h => hv (Finset.mem_union_left _ h)
    have hva : projV v a ∈ latV b v := by
      by_contra h
      exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, ha, (hbad a).mem_toFinset.2 h⟩))
    show cosVN b v (P v) (projV v a) = latV b v
    rw [hPT v hvT]
    exact cosVN_intSub b v hva
  · rw [hs Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    ext X
    show X - a ∈ L ↔ ∀ v, projV v X - projV v a ∈ lvN b v ((P v : OpenAddSubgroup (Fv F v)) : AddSubgroup (Fv F v)) n M
    constructor
    · intro h v i j k
      rw [← projV_subN]
      have := crd_projV b (X - a) v i j k
      rw [this]
      exact h i j k v
    · intro h i j k v
      have := crd_projV b (X - a) v i j k
      rw [← this, projV_subN]
      exact h v i j k

theorem isSchwartzArch_const_mulN {n M : ℕ} {φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ} (h : IsSchwartzArch φ) (c : ℂ) :
    IsSchwartzArch fun X => φ X * c := by
  obtain ⟨N, e, c1, c2, f, hf⟩ := h
  exact ⟨N, e, c1, c2, c • f, fun X => by simp [hf X, mul_comm]⟩

end GlobalTheory.CompanionTheory.WhitFree.DecN

namespace GlobalTheory.CompanionTheory.WhitFree

theorem schwartzBruhat_eq_sum_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → ∃ (k : ℕ) (φ : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin k → (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  obtain ⟨k', Φinf, Φf, hi, hf, hs⟩ := hΦ
  choose s A S hA hS hdec using fun i => DecN.exists_box_combN b (Φf i) (hf i)
  let I := Σ i : Fin k', ↥(s i)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun j X => Φinf (e.symm j).1 X * Φf (e.symm j).1 (e.symm j).2.1,
    fun j => A (e.symm j).1 (e.symm j).2.1, Finset.univ.biUnion S, fun j => ?_, fun j v => hA _ _ v,
    fun j v hv => ?_, fun X => ?_⟩
  · exact DecN.isSchwartzArch_const_mulN (hi _) _
  · refine hS _ _ (e.symm j).2.2 v fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩)
  · rw [hs X, Fintype.sum_equiv e.symm _ (fun p : I => pureN (fun Y => Φinf p.1 Y * Φf p.1 p.2.1) (A p.1 p.2.1) X)
      (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [pureN, mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WhitFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScaling
section
noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Dilate

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem gramR_dilate {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : R ⊗[F] E)
    (X : Fin 1 → Fin M → R ⊗[F] E) :
    gramR R σ J (fun p k => u * X p k) 0 0 = (u * sigR R σ u) * gramR R σ J X 0 0 := by
  simp only [gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem half_trace_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fv F v ⊗[F] E) (X : Fin 1 → Fin M → Fv F v ⊗[F] E), (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) X) = Algebra.norm (Fv F v) u * (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) X := by
  intro F E _ _ _ _ _ σ hσ M J hJ v u X
  beta_reduce
  have hX := GlobalTheory.CompanionTheory.SW.FibreRatio.gram_entry (Fv F v) hσ hJ X
  set r := algebraMap F (Fv F v) (1 / 2) *
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hr
  have hY : gramR (Fv F v) σ J (fun p k => u * X p k) 0 0 =
      (Algebra.norm (Fv F v) u * r) ⊗ₜ[F] (1 : E) := by
    have hN : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) u) = u * sigR (Fv F v) σ u :=
      GlobalTheory.Doubling.algebraMap_norm_eq hσ u
    rw [gramR_dilate, ← hN, hX,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp
  rw [hY]
  exact GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (Fv F v) hσ _

end GlobalTheory.CompanionTheory.AvgFree.Dilate
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingCompactFreeSet
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil

def dilHomeo {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (M : ℕ) (u : Aˣ) :
    (Fin 1 → Fin M → A) ≃ₜ (Fin 1 → Fin M → A) where
  toFun X p k := (u : A) * X p k
  invFun X p k := ((u⁻¹ : Aˣ) : A) * X p k
  left_inv X := by
    funext p k
    simp
  right_inv X := by
    funext p k
    simp
  continuous_toFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))
  continuous_invFun := continuous_pi fun p => continuous_pi fun k =>
    continuous_const.mul ((continuous_apply k).comp (continuous_apply p))

theorem linearIndependent_dil {A : Type} [CommRing A] {M : ℕ} (u : Aˣ) (X : Fin 1 → Fin M → A)
    (hX : LinearIndependent A X) :
    LinearIndependent A (fun (p : Fin 1) (k : Fin M) => (u : A) * X p k) := by
  rw [Fintype.linearIndependent_iff] at hX ⊢
  intro g hg i
  have h0 : ∑ i, (g i * (u : A)) • X i = 0 := by
    funext k
    have := congrFun hg k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h1 := hX (fun i => g i * (u : A)) h0 i
  exact (Units.mul_left_eq_zero u).1 h1

theorem dil_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v ⊗[F] E)ˣ) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsCompact P → IsOpen P → P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} → IsCompact ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ IsOpen ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P) ∧ (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  intro F E _ _ _ _ _ σ _ M v u P hc ho hP
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := TopK.isTopRing (Fv F v)
  refine ⟨hc.image (dilHomeo M u).continuous, (dilHomeo M u).isOpenMap _ ho, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact linearIndependent_dil u X (hP hX)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil
end
end

