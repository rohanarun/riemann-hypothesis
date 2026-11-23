module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCell
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSelfDualLatticeBoundedMajorantLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.SmGL.ParIndAdm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_finset_KO_cover (K : Subgroup (GL n k)) (hK : IsOpen (K : Set (GL n k))) :
    ∃ R : Finset (GL n k), ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K := by
  obtain ⟨R, hR⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n)).elim_finite_subcover
    (fun x : GL n k => (fun y => x⁻¹ * y) ⁻¹' (K : Set (GL n k)))
    (fun x => hK.preimage (by fun_prop))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [one_mem]⟩)
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨r, hr, h⟩ := Set.mem_iUnion₂.1 (hR hw)
  exact ⟨r, hr, h⟩

theorem eq_zero_of_fixed (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (K : Subgroup (GL n k))
    (R : Finset (GL n k)) (hR : ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K)
    (f : IndSp e ρ) (hf : f ∈ fixed (parInd e ρ) K) (h0 : ∀ r ∈ R, f.1.1 r = 0) : f = 0 := by
  have hfix : ∀ κ ∈ K, ∀ x, f.1.1 (x * κ) = f.1.1 x := fun κ hκ x => by
    have := congrArg (fun φ : IndSp e ρ => φ.1.1 x) (hf ⟨κ, hκ⟩)
    simpa using this
  apply Subtype.ext; apply Subtype.ext; funext x
  obtain ⟨u, l, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  obtain ⟨r, hr, hrw⟩ := hR w hw
  let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
    mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
  have hw' : f.1.1 w = 0 := by
    have := hfix _ hrw r
    rw [mul_inv_cancel_left] at this
    rw [this, h0 r hr]
  show f.1.1 ((p : GL n k) * w) = 0
  rw [parInd_law, hw', map_zero, smul_zero]

theorem isAdmissible_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    [FiniteDimensional ℂ W] : IsAdmissible (parInd e ρ) := by
  refine ⟨isSmooth_parInd e ρ, fun K hKo _ => ?_⟩
  obtain ⟨R, hR⟩ := exists_finset_KO_cover K hKo
  let L : fixed (parInd e ρ) K →ₗ[ℂ] (R → W) :=
    { toFun := fun f r => f.1.1.1 r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L fun f g hfg => ?_
  rw [← sub_eq_zero]
  have h := eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by
    have := congrFun hfg ⟨r, hr⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
    show f.1.1.1 r - g.1.1.1 r = 0
    rw [this, sub_self]
  exact Subtype.ext h

end GlobalTheory.SmGL.ParIndAdm

namespace GlobalTheory.ThK.MidJac

end GlobalTheory.ThK.MidJac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
section
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThK.RealLineGrowthDerivative
open GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

variable {J : Matrix (Fin n) (Fin n) E}

theorem prod_ofFn_snoc {G : Type} [Monoid G] {m : ℕ} (δ : Fin m → ℝ → G) (γ : ℝ → G) (s : Fin m → ℝ) (t : ℝ) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.snoc (α := fun _ => ℝ → G) δ γ i) (Fin.snoc (α := fun _ => ℝ) s t i)).prod =
      (List.ofFn fun i => δ i (s i)).prod * γ t := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem contDiff_partial_last {m : ℕ} {H : (Fin (m + 1) → ℝ) → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun s : Fin m → ℝ => deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 := by
  let v : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
  let L : (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i
  have hL : ∀ s t, Fin.snoc (α := fun _ => ℝ) s t = L s + t • v := fun s t => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [L, v]
    · simp [L, v, Fin.castSucc_ne_last]
  have hd : ∀ s, deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 = fderiv ℝ H (L s) v := fun s => by
    simp only [hL]
    have h1 : HasDerivAt (fun t : ℝ => L s + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (L s)
    have h2 := (hH.differentiable (by simp)).differentiableAt (x := L s + (0 : ℝ) • v)
    rw [zero_smul, add_zero] at h2
    have h3 := h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    exact h3.deriv
  simp only [hd]
  exact ((hH.fderiv_right (m := ∞) (by simp)).comp L.contDiff).clm_apply contDiff_const

theorem contDiff_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ (m : ℕ) (δ : Fin m → ℝ → GAd σ J),
      (∀ i, IsRealLine σ J (δ i)) → ∀ x,
      ContDiff ℝ ∞ fun s : Fin m → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => δ i (s i)).prod) := by
  intro l
  induction l with
  | nil => intro _ m δ hδ x; exact hf m δ hδ x
  | cons γ l ih =>
    intro hl m δ hδ x
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
    have hH := ih hl' (m + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ)
      (fun i => Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i) x
    have := contDiff_partial_last hH
    simp only [prod_ofFn_snoc, ← mul_assoc] at this
    simpa only [List.foldr_cons, lineDer] using this

theorem differentiableAt_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) (l : List (ℝ → GAd σ J))
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (x : GAd σ J) :
    DifferentiableAt ℝ (fun t => l.foldr lineDer f (x * γ t)) 0 := by
  have h := (contDiff_foldr_lineDer hf l hl 1 (fun _ => γ) (fun _ => hγ) x).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
  have h' := (h.differentiable (by simp)) 0
  have e : (fun t => l.foldr lineDer f (x * γ t)) = ((fun s : Fin 1 → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => (fun _ => γ) i (s i)).prod)) ∘ fun t : ℝ => fun _ : Fin 1 => t) := by
    funext t; simp
  rw [e]; exact h'

end GlobalTheory.ThK.RealLineGrowthDerivative

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumStabilizerGaussDecompositionBigCellStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v, GlobalTheory.DblVac.BigCell W v g →
      ∃ q ∈ GlobalTheory.DblVac.KD σ W v, q ∈ GlobalTheory.DblVac.PAnti σ W ∧ ∃ p ∈ GlobalTheory.DblVac.KD σ W v, p ∈ GlobalTheory.DblVac.PDiag σ W ∧ g = q * p := by
  first | exact @GlobalTheory.DblVacGauss.gauss_decomp | exact GlobalTheory.DblVacGauss.gauss_decomp | (intros; apply GlobalTheory.DblVacGauss.gauss_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleLeSpanExtremalTranslates
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem sqAct_sqAct_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g h : GL (Fin n) K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    sqAct K n lam g (sqAct K n lam h f) = sqAct K n lam (g * h) f := by
  unfold sqAct
  have hm := congrArg (fun φ => φ f) (Formalism.GradedWeylDivisibility.rowActMul K n n
    ((g : Matrix (Fin n) (Fin n) K)ᵀ) ((h : Matrix (Fin n) (Fin n) K)ᵀ))
  simp only [AlgHom.comp_apply] at hm
  rw [map_smul, hm, smul_smul, ← Matrix.transpose_mul]
  congr 1
  unfold detPow
  rw [map_mul, mul_zpow, Units.val_mul]

theorem sqAct_one_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam 1 f = f := by
  unfold sqAct detPow
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one, map_one, one_zpow, Units.val_one, one_smul]
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold Formalism.GradedWeylDivisibility.rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [h1]; rfl

theorem nablaSq_le_span_extremal : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n),
    nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  intro K _ _ n lam
  set M := Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) with hM
  have hanti : Antitone lam.natW := by
    intro i j hij
    have := lam.anti hij
    unfold DomWeight.natW
    omega
  have hext : extremal K n lam ∈ nablaSq K n lam :=
    Formalism.GradedWeylDivisibility.hwMem K n n le_rfl lam.natW hanti
  have hstab : ∀ g : GL (Fin n) K, ∀ f ∈ nablaSq K n lam, sqAct K n lam g f ∈ nablaSq K n lam := by
    intro g f hf
    unfold sqAct
    exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K n n lam.natW _ f hf)
  have hle : M ≤ nablaSq K n lam := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hstab g _ hext
  have hlin : ∀ g : GL (Fin n) K, ∀ (c : K) (f₁ f₂ : MvPolynomial (Fin n × Fin n) K),
      sqAct K n lam g (c • f₁ + f₂) = c • sqAct K n lam g f₁ + sqAct K n lam g f₂ := by
    intro g c f₁ f₂
    unfold sqAct
    rw [map_add (f := _), map_smul, smul_add, smul_comm]
  have hMstab : ∀ g : GL (Fin n) K, ∀ f ∈ M, sqAct K n lam g f ∈ M := by
    intro g f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [sqAct_sqAct_nabla]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero =>
      have h0 : sqAct K n lam g 0 = 0 := by unfold sqAct; simp
      rw [h0]; exact M.zero_mem
    | add x y _ _ hx hy =>
      have := hlin g 1 x y
      rw [one_smul, one_smul] at this
      rw [this]; exact M.add_mem hx hy
    | smul c x _ hx =>
      have hs : sqAct K n lam g (c • x) = c • sqAct K n lam g x := by
        unfold sqAct; rw [map_smul, smul_comm]
      rw [hs]; exact M.smul_mem c hx
  rcases _root_.GlobalTheory.AlcZero.nablaSq_simple_charZero K n lam M hle hMstab with h0 | h1
  · exfalso
    have hmem : extremal K n lam ∈ M := by
      have : sqAct K n lam 1 (extremal K n lam) ∈ M := Submodule.subset_span ⟨1, rfl⟩
      rwa [sqAct_one_nabla] at this
    rw [h0, Submodule.mem_bot] at hmem
    exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam.natW hmem
  · rw [h1]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSelfDualLatticeBoundedMajorantLeStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_selfDualLattice_bounded_majorant_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε R : ℝ), x ∈ X.dom → 0 < ε → 0 ≤ R → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({v | v ∈ X.L' ∧ ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ R}.encard : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 * Real.sqrt (R / ε)) ^ (2 * fdeg E * r)) := by
  first | exact @GlobalTheory.LatCount.encard_le | exact GlobalTheory.LatCount.encard_le | (intros; apply GlobalTheory.LatCount.encard_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfBaseChangeEqPowPrincipalAbelianCMTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem flat_surjective_spMap_ringOfIntegers (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K') :
    Flat (spMap (RingOfIntegers.mapRingHom j)) ∧ Surjective (spMap (RingOfIntegers.mapRingHom j)) := by
  letI : Algebra (𝓞 K) (𝓞 K') := (RingOfIntegers.mapRingHom j).toAlgebra
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K')) := by
    intro a b h
    apply RingOfIntegers.coe_injective
    apply j.injective
    exact congrArg ((↑) : 𝓞 K' → K') h
  haveI : FaithfulSMul (𝓞 K) (𝓞 K') := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : Module.Flat (𝓞 K) (𝓞 K') := inferInstance
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 K') := by
    constructor
    intro x
    exact IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral (R := ℤ) x)
  refine ⟨Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance), ⟨fun p => ?_⟩⟩
  let p' : PrimeSpectrum (𝓞 K) := p
  obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K') p'.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩

theorem eq_pow_of_baseChange_eq_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')
    (A B : PAT H (Sp (𝓞 K))) (A' B' : PAT H (Sp (𝓞 K'))) (mA : SABMap A'.t A.t (spMap (RingOfIntegers.mapRingHom j)))
    (mB : SABMap B'.t B.t (spMap (RingOfIntegers.mapRingHom j))) (g : A.t.G ⟶ B.t.G) (f' : A'.t.G ⟶ B'.t.G) (n : ℕ),
    0 < n → Serre.IsLinearHom A.t.act B.t.act g → Serre.IsLinearHom A'.t.act B'.t.act f' →
    (f' ^ n).left ≫ mB.φ = mA.φ ≫ g.left →
    ∃ f : A.t.G ⟶ B.t.G, Serre.IsLinearHom A.t.act B.t.act f ∧ f ^ n = g ∧ f'.left ≫ mB.φ = mA.φ ≫ f.left := by
  intro E _ _ _ H K K' _ _ _ _ j A B A' B' mA mB g f' n hn hg hf' hfg
  have hpow : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (m : ℕ), IsMonHom (𝟙 G ^ m) := by
    intro S G _ _ m
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ m) (𝟙 G) ≫ μ[G]))
  have hffs : ∀ {R : Type} [CommRing R] (P : PAT H (Sp R)), IsFinite (𝟙 P.t.G ^ n).left ∧
      Flat (𝟙 P.t.G ^ n).left ∧ Surjective (𝟙 P.t.G ^ n).left := by
    intro R _ P
    exact (ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow R P.t.G P.t.PP.L
      (P.t.PP.L.pull (fst P.t.G P.t.G).left) P.ab P.t.PP.isLB P.ample (LB.isLB_pull P.t.PP.isLB _)).2 n hn
  have hepi : ∀ {S : Scheme.{0}} {X Y : Over S} (u : X ⟶ Y), Flat u.left → Surjective u.left → Epi u := by
    intro S X Y u h1 h2
    haveI : Epi ((Over.forget S).map u) := Flat.epi_of_flat_of_surjective u.left
    exact (Over.forget S).epi_of_epi_map this
  obtain ⟨hAfin, hAfl, hAsu⟩ := hffs A
  obtain ⟨-, hA'fl, hA'su⟩ := hffs A'
  have hq : QuasiCompact (𝟙 A.t.G ^ n).left := inferInstance
  obtain ⟨hflatj, hsurj⟩ := flat_surjective_spMap_ringOfIntegers K K' j
  have hker : ∀ (T : Over (Sp (𝓞 K))) (x : T ⟶ A.t.G), x ≫ (𝟙 A.t.G ^ n) = 1 → x ≫ g = 1 := by
    intro T x hx
    have hb : pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom =
        pullback.snd T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ spMap (RingOfIntegers.mapRingHom j) :=
      pullback.condition
    obtain ⟨eA, heA⟩ := exists_mulEquiv_of_isGrpPullback mA.cart _ _ hb
    obtain ⟨eB, heB⟩ := exists_mulEquiv_of_isGrpPullback mB.cart _ _ hb
    let prO : Over.mk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j)) ≫ T.hom) ⟶ T :=
      Over.homMk (pullback.fst T.hom (spMap (RingOfIntegers.mapRingHom j))) rfl
    have hE : Epi prO := by
      haveI := hflatj
      haveI := hsurj
      exact hepi prO (inferInstanceAs (Flat (pullback.fst _ _))) (inferInstanceAs (Surjective (pullback.fst _ _)))
    have hxn : x ^ n = 1 := by rw [← hx, MonObj.comp_pow, Category.comp_id]
    have hx' : eA.symm (prO ≫ x) ^ n = 1 := by
      apply eA.injective
      rw [map_pow, map_one, MulEquiv.apply_symm_apply, ← MonObj.comp_pow, hxn, MonObj.comp_one]
    have e2 : eA.symm (prO ≫ x) ≫ (f' ^ n) = 1 := by
      haveI := hf'.isMonHom
      rw [MonObj.comp_pow, ← MonObj.pow_comp, hx', MonObj.one_comp]
    have e1 : eB (eA.symm (prO ≫ x) ≫ (f' ^ n)) = prO ≫ x ≫ g := by
      apply Over.OverMorphism.ext
      rw [heB, Over.comp_left, Category.assoc, hfg, ← Category.assoc, ← heA, MulEquiv.apply_symm_apply]
      simp only [Over.comp_left, Category.assoc]
    have : prO ≫ (x ≫ g) = prO ≫ 1 := by rw [← e1, e2, map_one, MonObj.comp_one]
    exact (cancel_epi prO).1 this
  haveI := hg.isMonHom
  haveI := hpow A.t.G n
  obtain ⟨⟨ψ, hψ, hψg⟩, hEpiA⟩ := exists_monHom_factor_of_flat_surjective _ A.t.G A.t.G B.t.G (𝟙 A.t.G ^ n) g
    (hpow _ n) hg.isMonHom hAfl hAsu hq hker
  haveI := hψ
  have hψn : ψ ^ n = g := by rw [← hψg, MonObj.pow_comp, Category.id_comp]
  have hlin : Serre.IsLinearHom A.t.act B.t.act ψ := by
    refine ⟨hψ, fun c => ?_⟩
    haveI := A.t.act.hom c
    rw [← cancel_epi (𝟙 A.t.G ^ n)]
    have hc : (𝟙 A.t.G ^ n) ≫ A.t.act.act c = A.t.act.act c ≫ (𝟙 A.t.G ^ n) := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    rw [reassoc_of% hc, hψg, reassoc_of% hψg]
    exact hg.comm c
  obtain ⟨w, hw, hwc⟩ := PairingFibre.exists_hom mA.cart mB.cart ψ
  haveI := hw
  haveI := hf'.isMonHom
  have hφ : mA.φ ≫ A.t.G.hom = A'.t.G.hom ≫ spMap (RingOfIntegers.mapRingHom j) := mA.cart.1.w
  have hpw : ∀ m : ℕ, (w ^ (m + 1)).left ≫ mB.φ = mA.φ ≫ (ψ ^ (m + 1)).left := by
    intro m
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hwc
    | succ m ih =>
      rw [pow_succ w, pow_succ ψ]
      exact FamDesc.exists_mul hφ mB.cart ih hwc
  have hwn : w ^ n = f' ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    apply Over.OverMorphism.ext
    apply mB.cart.1.hom_ext
    · rw [hpw m, hψn, hfg]
    · rw [Over.w, Over.w]
  have hwf : w = f' := by
    haveI := hepi (𝟙 A'.t.G ^ n) hA'fl hA'su
    rw [← cancel_epi (𝟙 A'.t.G ^ n), MonObj.pow_comp, MonObj.pow_comp, Category.id_comp, Category.id_comp, hwn]
  refine ⟨ψ, hlin, hψn, ?_⟩
  rw [← hwf]
  exact hwc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelEquivCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.FieldBC GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem isBC_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    IsBC hle (rulBC hle f) (fun _ : Fin 1 => (1 : c'.F)) (fun _ => f) := by
  intro S _ _ _ h y
  rw [((_root_.GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 S h y]
  simp

end Field

section Action

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem actLev_mem_sec (hL : ActLev (Xo := Xo) c lev) (g : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : actLev c lev g f ∈ sec Xo c a n :=
  actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hf

end Action

section Weights

variable {D : D7}

end Weights

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} {i : Fin D.R.m}

theorem inR (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

section Second

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Y : RowDat T G i) (R : RealDat D A Ks)

end Second

variable [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0}


variable {O : OMDat T.toCore R i Tp tup} {Y : RowDat T G i}


end Compare

end GlobalTheory.LevelEquivCompare
end
end

