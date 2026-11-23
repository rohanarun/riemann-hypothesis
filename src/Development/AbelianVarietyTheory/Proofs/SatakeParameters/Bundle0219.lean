module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubspaceTrivialOutsideSplitPlac
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponent
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAtStandardPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0192

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExists
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLocal


open Formalism.IndefR.principalLevelFrame in
theorem finTyp_fixed_finiteDimensional : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (X : RowMod D rep j) (σ : D.what₂.FT), Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ → ∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f}) := by
  intro D rep j X σ hne N hN
  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : (rep σ).S →ₗ[ℂ] X.A,
      (IsEqvA X.ρ (rep σ) Φ ∧ LinearMap.range Φ ≤ X.C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hne
    unfold Formalism.IndefR.principalLevelFrame.isotIn
    exact iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    let S' : Submodule ℂ (GAf D.host.E D.R.r → ℂ) := (LinearMap.ker Φ).map (rep σ).S.subtype
    have hS'le : S' ≤ (rep σ).S := by
      rintro f ⟨k, _, rfl⟩
      exact k.2
    have hS'st : ∀ h, ∀ f ∈ S', NG.rt D.host.E D.R.r h f ∈ S' := by
      rintro h f ⟨k, hk, rfl⟩
      refine ⟨⟨NG.rt D.host.E D.R.r h k, (rep σ).stable h k k.2⟩, ?_, rfl⟩
      show Φ _ = 0
      rw [hΦe h k, LinearMap.mem_ker.1 hk, map_zero]
    rcases (rep σ).irr S' hS'le hS'st with h0 | hall
    · rw [eq_bot_iff]
      intro k hk
      have : (k : GAf D.host.E D.R.r → ℂ) ∈ S' := ⟨k, hk, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E D.R.r → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      rw [show y = k from Subtype.ext hky.symm]
      exact (Submodule.mem_bot ℂ).2 (LinearMap.mem_ker.1 hk)
  set F := Submodule.span ℂ {f | f ∈ (rep σ).S ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → NG.rt D.host.E D.R.r κ f = f} with hF
  set T := Submodule.span ℂ {x | x ∈ X.C ∧ ∀ κ, NG.Cong D.host.E D.R.r N κ → X.ρ κ x = x} with hT
  have := X.adm N hN
  have hFS : F ≤ (rep σ).S := Submodule.span_le.2 fun f hf => hf.1
  have hFT : ∀ f (hf : f ∈ F), Φ ⟨f, hFS hf⟩ ∈ T := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ⟨hΦC ⟨_, rfl⟩, fun κ hκ => ?_⟩
      rw [← hΦe κ]
      congr 1
      exact Subtype.ext (hx.2 κ hκ)
    | zero =>
      have : (⟨0, hFS F.zero_mem⟩ : (rep σ).S) = 0 := rfl
      rw [this, map_zero]
      exact T.zero_mem
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hFS (F.add_mem hx hy)⟩ : (rep σ).S) = ⟨x, hFS hx⟩ + ⟨y, hFS hy⟩ := rfl
      rw [this, map_add (f := _)]
      exact T.add_mem ihx ihy
    | smul a x hx ih =>
      have : (⟨a • x, hFS (F.smul_mem a hx)⟩ : (rep σ).S) = a • ⟨x, hFS hx⟩ := rfl
      rw [this, map_smul]
      exact T.smul_mem a ih
  let g : F →ₗ[ℂ] T := LinearMap.codRestrict T (Φ ∘ₗ Submodule.inclusion hFS) (fun f => hFT f f.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : Φ (Submodule.inclusion hFS a) = Φ (Submodule.inclusion hFS b) := congrArg Subtype.val hab
    exact Submodule.inclusion_injective hFS (hinj h1)
  exact Module.Finite.of_injective g hg

end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

section Asm
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem isLocS_of_irr (π : NG.FinTyp L n) (s : SplitPlace L) (W : Submodule ℂ (GAf L n → ℂ)) (hWS : W ≤ π.S)
    (hW0 : W ≠ ⊥) (hst : ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W, NG.rt L n x f ∈ W)
    (hirr : ∀ W' : Submodule ℂ (GAf L n → ℂ), W' ≤ W →
      (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ W', NG.rt L n x f ∈ W') → W' = ⊥ ∨ W' = W) :
    ∃ τ, IsLocS π.S s τ := by
  first
  | exact @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component
  | (apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply _root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> assumption)
  | (intros; apply @_root_.GlobalTheory.blockFieldPairProjections.exists_local_component <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.blockFieldPairProjections.exists_local_component ..)

end Asm
end GlobalTheory.RowLocal

namespace GlobalTheory.RowLocal

theorem finTyp_exists_isLocS : ∀ (D : D7) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (j : ℕ) (_ : RowMod D rep j) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ, IsLocS (rep σ).S s τ := by
  intro D rep j X σ hσ s
  have hB00 : X.B 0 0 = 0 := by
    have h := X.lin 0 X.C.zero_mem 0 X.C.zero_mem 0 X.C.zero_mem 1
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hne : Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (rep σ) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
    have hmem := (X.isot σ y).1 hy
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hy0
    have h := X.φ_inner y y
    rw [hmem, hB00] at h
    exact inner_self_eq_zero.1 h
  obtain ⟨B', hlin, hherm, hpos, hinv⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos
    X.stab X.inv (rep σ) hne
  obtain ⟨W, hWS, hW0, hst, hirr⟩ := _root_.GlobalTheory.exists_irreducible_sub_trivOutside_split D.host.E D.R.r (rep σ) B' hlin hherm hpos hinv (finTyp_fixed_finiteDimensional D rep j X σ hne) s
  exact isLocS_of_irr (rep σ) s W hWS hW0 hst hirr

end GlobalTheory.RowLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaFamilyNormalisedAllPlaces
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem tPull_comp (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E)
    (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₂ γ₂' (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₁ γ₁' z) =
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (γ₁' * γ₂') z := by
  funext τ
  show (Matrix.conjTranspose (γ₂'.map (TaylorLogMetric.embT D τ)) *
      (Matrix.conjTranspose (γ₁'.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * γ₁.map (TaylorLogMetric.embT D τ)) *
      γ₂.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) =
    (Matrix.conjTranspose ((γ₁' * γ₂').map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (γ₁ * γ₂).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem tPull_one (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E)
      (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ
  show (Matrix.conjTranspose ((1 : Matrix (Fin N') (Fin N') D.host.E).map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) = z τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem smulLat_star_smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (hγ : star γ * γ = 1)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    SDLat.smulLat (star γ) (SDLat.smulLat γ M) = M := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp]
  have h : ((Matrix.toLin' (star γ)).restrictScalars (𝓞 D.host.E)).comp ((Matrix.toLin' γ).restrictScalars (𝓞 D.host.E)) =
      LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.toLin' (star γ) (Matrix.toLin' γ x) = x
    rw [← Matrix.toLin'_mul_apply, hγ, Matrix.toLin'_one, LinearMap.id_apply]
  rw [h, Submodule.map_id]

theorem mem_La_smulLat_iff (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : TaylorLogMetric.VC D N N') :
    x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') ↔
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M' := by
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Matrix.mem_unitaryGroup_iff'.mp γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  constructor
  · intro hx
    exact Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
  · intro hx
    have h3 : star (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 := by
      rw [star_star]; exact h2'
    have h := Formalism.L2.KerInert.ie_La_pull cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
      (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) h3 (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')
    rw [smulLat_star_smulLat _ h1, smulLat_star_smulLat _ h1'] at h
    have h4 := h hx
    rw [AddSubgroup.mem_comap] at h4
    have e : Formalism.L2.KerInert.ieTPullHom cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
        (star (γ' : Matrix (Fin N') (Fin N') D.host.E))
        (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E) x) = x := by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ x) = x
      rw [tPull_comp, h2, h2', tPull_one]
    rw [e] at h4
    exact h4

end GlobalTheory.ThLoc.AllPlaces

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem formV_eq_Hf (u v : TaylorLogMetric.VC D N N') :
    formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' u v = TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) u v := rfl

def tPullLin (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

def tPullEquiv (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  LinearEquiv.ofLinearMap (tPullLin cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E))
    (tPullLin cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E)) (star (γ' : Matrix (Fin N') (Fin N') D.host.E)))
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff'.mp γ.2, Matrix.mem_unitaryGroup_iff'.mp γ'.2, tPull_one])
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.mem_unitaryGroup_iff.mp γ'.2, tPull_one])

end GlobalTheory.ThLoc.AllPlaces


open GlobalTheory.ThLoc.AllPlaces in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem GlobalTheory.ThLoc.latAt_all : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  intro D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hA p _ ι
  have hp : p.Prime := Fact.out
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨hN, hN', hL, hL'⟩ := hA
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  have hAM : TaylorLogMetric.admitted D N N' M M' := ⟨hN, hN', hM, hM'⟩
  have hAL : TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', hL, hL'⟩
  have hStd := _root_.GlobalTheory.ThLoc.LocStd.latAt_std D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' M M' hAM p ι hEq hEq'

  let φ : (DVar X.Tau N N' → ℂ) ≃ₗ[ℂ] (DVar X.Tau N N' → ℂ) :=
    (s.flatV N N').trans ((tPullEquiv cc δ γ γ').trans (s.flatV N N').symm)
  have hφ : ∀ z, s.flatV N N' (φ z) = Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (s.flatV N N' z) := fun z => by
    show s.flatV N N' ((s.flatV N N').symm (tPullEquiv cc δ γ γ' (s.flatV N N' z))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hI : IsIsom (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _) := by
    intro x y
    show matH _ (φ x) (φ y) = _
    rw [KS.Lat.form_flat s, KS.Lat.form_flat s, hφ, hφ, formV_eq_Hf, formV_eq_Hf,
      Formalism.L2.KerInert.PullbackComparison.Hf_tPull cc δ _ _ (Matrix.mem_unitaryGroup_iff.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)]
  have hloc := _root_.GlobalTheory.ThLoc.LocPull.locNorm_pull a₀ b₀ D.host.d ha hd lam hlam (DVar X.Tau N N') _ (s.laF B.tor M M')
    (fun z => B.eNat χ N N' M M' (s.flatV N N' z)) p ι φ hI hStd.locNorm
  have hΛ : (s.laF B.tor M M').comap (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _).toAddMonoidHom = s.laF B.tor L L' := by
    ext x
    show s.flatV N N' (φ x) ∈ TaylorLogMetric.La D B.tor M M' ↔ s.flatV N N' x ∈ TaylorLogMetric.La D B.tor L L'
    rw [hφ, hLM, hLM']
    exact (mem_La_smulLat_iff γ γ' M M' _).symm
  have hθ : (fun z => B.eNat χ N N' M M' (s.flatV N N' (φ z))) = fun z => B.eNat χ N N' L L' (s.flatV N N' z) := by
    funext z
    rw [hφ, hLM, hLM']
    have h := (Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ).1 N N' ⟨M, hM⟩ ⟨M', hM'⟩ hN hN' γ γ'
    exact congrFun h (s.flatV N N' z)
  rw [hΛ] at hloc
  simp only [hθ] at hloc
  exact ⟨hcm, KS.Lat.selfDual_laF s B hcc hδ hAL, fun x hx => KS.Lat.theta_laF s B (KS.Lat.odd_of_cmOK hcm) hx,
    KS.Lat.eNat_laF s B hcc hδ χ hAL, hloc⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalTwistOfBlockTypeVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.BlockSph

theorem sph_of_isBlockVec : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (π₁ : Irr k r) (π₂ : Irr k t) (v : π.V), IsSmoothChar χ → IsTame χ → (∀ α : ℂˣ, ¬ InSupport π₁.π (χ * unrChar k α)) → Nonempty (π.π.Equiv (prod₂ π₁.π π₂.π)) → v ≠ 0 → IsBlockVec χ π.π v → IsSpherical (twist π₂.π (detChar (Fin t) χ⁻¹)) := by
  intro hBZ hG hDZ k _ _ _ _ r t χ π π₁ π₂ v hχ hχt hsupp ⟨φ⟩ hv hblk
  obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd k r t _ _ π₁.π π₂.π
  let Ψ := φ.trans E
  have hsm : IsSmooth (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) :=
    isSmooth_parInd _ _
  have hirr : (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)).IsIrreducible :=
    (MultiIrr.isIrreducible_iff_of_equiv Ψ).1 π.irr
  have hv' : Ψ v ≠ 0 := fun h => hv (Ψ.injective (h.trans (map_zero Ψ).symm))
  have hblk' : IsBlockVec χ (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)) (Ψ v) :=
    fun h hh h1 h2 u hu => by
      have := Ψ.toIntertwiningMap.isIntertwining _ _ h v
      rw [hblk h hh h1 h2 u hu, map_smul] at this
      exact this.symm
  obtain ⟨hx0, hx⟩ := _root_.GlobalTheory.JacBlockTwo.jacquet_ne_zero_of_isBlockVec_two hDZ k r t χ _ _ (Ψ v) hsm hirr hχt hv' hblk'
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy⟩ := _root_.GlobalTheory.EigenSubquot.exists_irreducible_subquotient_eigen _ _ (GlobalTheory.SmGL.jac (two (stdSum (rfl : r + t = r + t)))
    (multiProd (two (stdSum (rfl : r + t = r + t))) (Exponents.twoRep π₁.π π₂.π)))
    {h | ∃ g ∈ KO k (Fin t), h = Pi.mulSingle true g}
    (fun h => (χ (Matrix.GeneralLinearGroup.det (h true)) : ℂ)) _ hx0
    (by rintro _ ⟨g, hg, rfl⟩; simpa using hx g hg)
  have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact π₁.smooth
    · exact π₂.smooth
  have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
    cases i
    · exact hasFiniteLength_of_isIrreducible π₁.irr
    · exact hasFiniteLength_of_isIrreducible π₂.irr
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ hsub
  obtain ⟨z, hz0, hz⟩ := _root_.GlobalTheory.EigenFactor.exists_eig_factor k Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (g j) fun i => (s i j).ρ)
    Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0
    (fun h hh => by simpa using hy (Pi.mulSingle true h) ⟨h, hh, rfl⟩)
  obtain ⟨w, hw0, hw⟩ := _root_.GlobalTheory.SphBlock.exists_eigen_at_one k Bool (fun i => Fin (b.1 i true)) (Fin t) (g true) _ (fun i => (s i true).ρ) χ z hz0 hz
  by_cases hm : b.1 false true = 0
  · obtain ⟨z', hz'0, hz'⟩ := _root_.GlobalTheory.EigenFactor.exists_eig_factor k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) true χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw true)
    have hc : b.1 true false = 0 := by
      have h1 := b.2.1 true
      have h2 := b.2.2 true
      simp [Fintype.sum_bool] at h1 h2
      omega
    exact _root_.GlobalTheory.EmptyFirstBlock.isSpherical_twist_of_empty_block k t _ π₂.π (b.1 true) (f true) (s true) χ z' π₂.smooth π₂.irr hc (hrow true) hz'0 hz'
  · obtain ⟨z', hz'0, hz'⟩ := _root_.GlobalTheory.EigenFactor.exists_eig_factor k Bool (fun i => Fin (b.1 i true)) _ (fun i => (s i true).ρ) _
      (piTensor fun i => (s i true).ρ) false χ w (fun i => (s i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
    obtain ⟨α, hα⟩ := _root_.GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen hBZ hG hDZ k _ _ (s false true).ρ χ z' (s false true).smooth (s false true).irr hχ
      (Nat.pos_of_ne_zero hm) hz'0 hz'
    exact absurd (_root_.GlobalTheory.SuppStage.main hBZ hG k r _ π₁.π Bool (b.1 false) (f false) (s false) true _ π₁.smooth (hrow false) hα) (hsupp α)

end GlobalTheory.BlockSph
end

