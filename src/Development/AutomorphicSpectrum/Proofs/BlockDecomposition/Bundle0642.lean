module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0636
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlocksExponent
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DlBridgeAt

theorem val_eq_uniformizer_of_ord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (h : ord k ϖ = 1) :
    valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact uniformizer_ne_zero hy.symm
  have hu : valuation k ((Units.mk0 y hy0 : kˣ) : k) = uniformizer k := hy
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hu
  have h2 : ord k (ϖ * (Units.mk0 y hy0)⁻¹) = 0 := by
    have h3 := ord_mul k (ϖ * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right] at h3
    omega
  have h4 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu] at h4
  have hne : uniformizer k ≠ 0 := uniformizer_ne_zero
  exact (mul_inv_eq_one₀ hne).1 h4

end GlobalTheory.CompanionTheory.DlBridgeAt


open GlobalTheory.CompanionTheory.DlBridgeAt in
theorem GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  intro E _ _ _ w ϖ hϖ
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  refine ⟨val_eq_uniformizer_of_ord ϖ hord, fun N x => ?_⟩
  have hinv := GlobalTheory.CompanionTheory.JacEigAt.deltaHalf_inv N w ϖ hord x
  have hv := val_deltaHalf (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  have hm := deltaB_eq_modulus (fun i : Fin N => ϖ ^ x i)
  have hpos := modulus_pos (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  rw [Units.val_inv_eq_inv_val, hv] at hinv
  rw [hv, hm]
  change _ = GlobalTheory.BCT.qh w ^ _ at hinv
  rw [← hinv]
  set m := modulus (w.adicCompletion E) (fun _ : Fin N => Unit)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) with hmdef
  have hs : √m * √m = m := Real.mul_self_sqrt hpos.le
  have hs0 : √m ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : ∀ s : ℝ, s ≠ 0 → (s * s)⁻¹ * s = s⁻¹ := fun s h => by field_simp
  have h5 := key _ hs0
  rw [hs] at h5
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, h5]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightTraceFormula
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.CharDec

variable {n : ℕ}

theorem core (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H)
    (hg : Formalism.REAL.GlRel G) (hh : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
        HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) :
    ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S) = ∑ ν ∈ F, trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  classical
  have hp : ∀ ν : Fin n → ℤ, Antitone ν → ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧
      (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z :=
    fun ν hν => _root_.GlobalTheory.CompanionTheory.RealCountG.Isotypic.exists_isotypic_projection H ρ G ν hg hh hd hν
  choose! p hpG hpid hpkill hptr using hp
  obtain ⟨Fs, hFs⟩ : ∃ Fs : Set (Fin n → ℤ), ∀ ν, ν ∈ Fs ↔ Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥ :=
    ⟨{ν | Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥}, fun ν => Iff.rfl⟩
  have hfin : Fs.Finite := by
    have hv : ∀ ν ∈ Fs, ∃ v ∈ hwOf G (wtR ν), v ≠ 0 := fun ν hν =>
      Submodule.exists_mem_ne_zero_of_ne_bot ((hFs ν).1 hν).2
    choose! v hvmem hvne using hv
    have hli : LinearIndependent ℂ (fun ν : Fs => v ν) := by
      rw [linearIndependent_iff']
      intro s g hs i hi
      have hia : Antitone (i : Fin n → ℤ) := ((hFs i).1 i.2).1
      have h1 := congrArg (p i) hs
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero, Finset.sum_eq_single i] at h1
      · rw [map_smul, hpid i hia (v i) (hvmem i i.2)] at h1
        exact (smul_eq_zero.mp h1).resolve_right (hvne i i.2)
      · intro j _ hji
        rw [map_smul, hpkill i hia (wtR j) (v j) (fun heq => hji (Subtype.ext (wtR_injective heq)))
          (hvmem j j.2), smul_zero]
      · intro hi'
        exact absurd hi hi'
    exact Set.finite_coe_iff.mp hli.finite
  have hF : ∀ ν, ν ∈ hfin.toFinset ↔ Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥ := fun ν => by
    rw [Set.Finite.mem_toFinset, hFs]
  have hcomm : ∀ a b w, (LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) (G a b w) =
      G a b ((LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) w) := by
    intro a b w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply, map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun ν hν => hpG ν ((hF ν).1 hν).1 a b w
  have hhigh : ∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v →
      (LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) v = 0 := by
    intro μ v hK
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    obtain ⟨ν₀, rfl⟩ := _root_.GlobalTheory.CompanionTheory.RealCountG.WtInt.weight_integral H ρ G hd μ v hv0 hK.1
    have hanti : Antitone ν₀ := by
      have h := _root_.GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable H G ⊤ (wtR ν₀) v hg inferInstance (fun _ _ _ _ => Submodule.mem_top)
        Submodule.mem_top hv0 hK
      intro i j hij
      have := h hij
      simp only [wtR] at this
      exact_mod_cast this
    have hmem : v ∈ hwOf G (wtR ν₀) := hK
    have hin : ν₀ ∈ hfin.toFinset := (hF ν₀).2 ⟨hanti, fun hbot => hv0 (by
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).1 hmem)⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply]
    rw [Finset.sum_eq_single ν₀, hpid ν₀ hanti v hmem, sub_self]
    · intro ν hν hne
      exact hpkill ν ((hF ν).1 hν).1 (wtR ν₀) v (fun heq => hne (wtR_injective heq).symm) hK
    · intro h
      exact absurd hin h
  have hsum : ∑ ν ∈ hfin.toFinset, p ν = LinearMap.id :=
    (sub_eq_zero.mp (GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest H H G G hg hh _ hcomm hhigh)).symm
  refine ⟨hfin.toFinset, fun ν hν => ((hF ν).1 hν).1, fun ν hν hνF => ?_, ?_⟩
  · by_contra hne
    exact hνF ((hF ν).2 ⟨hν, hne⟩)
  · intro S hS k z hk hz
    calc LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S)
        = LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ ∑ ν ∈ hfin.toFinset, p ν) := by
          rw [hsum, LinearMap.comp_id]
      _ = ∑ ν ∈ hfin.toFinset, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p ν) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← map_sum]
          congr 1
          ext w
          set_option synthInstance.maxHeartbeats 100000 in
            simp [LinearMap.sum_apply, map_sum]
      _ = _ := Finset.sum_congr rfl fun ν hν => hptr ν ((hF ν).1 hν).1 S hS k z hk hz

theorem sum_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (x : Fin n → Fin n → M) (a b : Fin n) (c : ℂ) :
    ∑ i, ∑ j, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) i j • x i j = c • x a b := by
  classical
  rw [Finset.sum_eq_single a (fun i _ hi => Finset.sum_eq_zero fun j _ => by
        simp [Ne.symm hi]) (by simp),
      Finset.sum_eq_single b (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

theorem eq_zero_of_skew {M : Type*} [AddCommGroup M] [Module ℂ M] (x : Fin n → Fin n → M)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ i, ∑ j, X i j • x i j = 0) (a b : Fin n) : x a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [Matrix.conjTranspose_sub, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT,
      star_one, neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [Matrix.conjTranspose_add, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT,
      Complex.star_def, Complex.conj_I, GlobalTheory.CompanionTheory.RealCount.InjHw.single_negI, GlobalTheory.CompanionTheory.RealCount.InjHw.single_negI,
      neg_add, add_comm])
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single', one_smul] at h1 h2
  rw [sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul] at h2
  exact (smul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)

theorem trOn_transport {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N)
    (D : Submodule ℂ M) (D' : Submodule ℂ N) (hD : ∀ x, x ∈ D ↔ e x ∈ D') (f : M →ₗ[ℂ] M) (g : N →ₗ[ℂ] N)
    (hfg : ∀ x, e (f x) = g (e x)) (hf : ∀ x ∈ D, f x ∈ D) : trOn D f = trOn D' g := by
  have hg : ∀ y ∈ D', g y ∈ D' := by
    intro y hy
    have hx : e.symm y ∈ D := (hD _).2 (by simpa using hy)
    have := (hD _).1 (hf _ hx)
    rwa [hfg, LinearEquiv.apply_symm_apply] at this
  have hmap : D.map (e : M →ₗ[ℂ] N) = D' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hD x).1 hx
    · intro hy
      exact ⟨e.symm y, (hD _).2 (by simpa using hy), by simp⟩
  delta trOn
  rw [dite_eq_left hf, dite_eq_left hg, ← LinearMap.trace_conj' (f.restrict hf) (e.ofSubmodules D D' hmap)]
  congr 1
  ext y
  simp [LinearEquiv.conj_apply, hfg]

theorem main : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G →
    ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
        LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
          ∑ ν ∈ F, trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) * weylChar ν z := by
  intro n E T hT G hG
  obtain ⟨e, ρ', hρc, hρn, he⟩ := _root_.GlobalTheory.CompanionTheory.RealCount.dualRep_exists E
  obtain ⟨G', hg', hh', hd'⟩ :=
    _root_.GlobalTheory.CompanionTheory.RealCount.DerivRep.derivative_of_rep (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) ρ' hρc hρn
  have : FiniteDimensional ℂ (E.V →L[ℂ] ℂ) := LinearEquiv.finiteDimensional e.symm
  have hint : ∀ a b ξ, e (G a b ξ) = G' a b (e ξ) := by
    intro a b ξ
    have hx : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
        ∑ i, ∑ j, X i j • (e (G i j ξ) - G' i j (e ξ)) = 0 := by
      intro X hX
      obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ,
          ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) :=
        ⟨GlobalTheory.CompanionTheory.RealCount.InjHw.expU X hX, fun t => rfl⟩
      have h1 := hG.2 X γ hX hγ ξ
      have h2 := hd' X γ hX hγ (e ξ)
      have h3 : HasDerivAt (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) (e (∑ a, ∑ b, X a b • G a b ξ)) 0 := by
        exact (e.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) h1
      have h4 : (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) = fun t => ρ' (γ t) (e ξ) := funext fun t => he (γ t) ξ
      rw [h4] at h3
      have h5 := h3.unique h2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul] at h5
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [h5, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_skew (fun i j => e (G i j ξ) - G' i j (e ξ)) hx a b)
  have hint2 : ∀ a b w, e.symm (G' a b w) = G a b (e.symm w) := fun a b w =>
    e.injective (by rw [hint, e.apply_symm_apply, e.apply_symm_apply])
  have hcommT : ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := _root_.GlobalTheory.CompanionTheory.RealCountG.DualComm.dualT_G E T hT G hG
  obtain ⟨S', hS'⟩ : ∃ S' : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)), ∀ w, S' w = e (dualT E T (e.symm w)) :=
    ⟨e.conj (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)), fun w => by simp [LinearEquiv.conj_apply]⟩
  have hS'comm : ∀ a b w, S' (G' a b w) = G' a b (S' w) := by
    intro a b w
    rw [hS', hS', hint2, hcommT, hint]
  have hmem : ∀ (μ : Fin n → ℝ) (v : E.V →L[ℂ] ℂ), v ∈ hwOf G μ ↔ e v ∈ hwOf G' μ := by
    intro μ v
    change Formalism.REAL.KHighest (fun _ => true) G μ v ↔ Formalism.REAL.KHighest (fun _ => true) G' μ (e v)
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun a => by rw [← hint, h1 a, map_smul], fun a b hab hε => by rw [← hint, h2 a b hab hε, map_zero]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun a => e.injective ?_, fun a b hab hε => e.injective ?_⟩
      · rw [hint, h1 a, map_smul]
      · rw [hint, h2 a b hab hε, map_zero]
  have hpres : ∀ μ : Fin n → ℝ, ∀ x ∈ hwOf G μ, dualT E T x ∈ hwOf G μ := by
    intro μ x hx
    change Formalism.REAL.KHighest (fun _ => true) G μ x at hx
    change Formalism.REAL.KHighest (fun _ => true) G μ (dualT E T x)
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight at hx ⊢
    exact ⟨fun a => by rw [← hcommT, hx.1 a, map_smul],
      fun a b hab hε => by rw [← hcommT, hx.2 a b hab hε, map_zero]⟩
  have hfg : ∀ x, e ((dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) x) = S' (e x) := fun x => by
    simp [hS']
  obtain ⟨F, hFa, hFbot, htr⟩ := core _ ρ' G' hg' hh' hd'
  refine ⟨F, hFa, fun ν hν hνF => ?_, ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    have h' : e v ∈ hwOf G' (wtR ν) := (hmem _ v).1 hv
    rw [hFbot ν hν hνF, Submodule.mem_bot] at h'
    exact (Submodule.mem_bot ℂ).2 (e.map_eq_zero_iff.mp h')
  · intro k z hk hz
    have hconj : e.conj (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
        (ρ' k : _ →ₗ[ℂ] _) ∘ₗ S' := by
      apply LinearMap.ext
      intro w
      rw [LinearMap.comp_apply, hS', ContinuousLinearMap.coe_coe, ← he]
      show e (dualT E (E.ρ k⁻¹ * T) (e.symm w)) = _
      congr 1
      simp only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      rw [← hT k⁻¹, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    rw [← LinearMap.trace_conj' (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) e, hconj,
      htr S' hS'comm k z hk hz]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [trOn_transport e (hwOf G (wtR ν)) (hwOf G' (wtR ν)) (hmem _) _ S' hfg (hpres _)]

end GlobalTheory.CompanionTheory.RealCountG.CharDec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
section
noncomputable section

namespace GlobalTheory.CompanionTheory.FarSeries

open PositivityTheory.RgEis PositivityTheory.Rg.SwEis _root_.Topology

theorem exp_mul_le {a b x s t L : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) (hL : |s - t| ≤ L) :
    Real.exp (x * s) ≤ Real.exp ((|a| + |b|) * L) * (Real.exp (a * t) + Real.exp (b * t)) := by
  have hx : |x| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b]
    · linarith [le_abs_self b, abs_nonneg a]
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have h3 : x * (s - t) ≤ (|a| + |b|) * L :=
    calc x * (s - t) ≤ |x * (s - t)| := le_abs_self _
      _ = |x| * |s - t| := abs_mul _ _
      _ ≤ (|a| + |b|) * L := mul_le_mul hx hL (abs_nonneg _) (by positivity)
  have h4 : Real.exp (x * t) ≤ Real.exp (a * t) + Real.exp (b * t) := by
    rcases le_total 0 t with ht | ht
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h2 ht)
      linarith [Real.exp_pos (a * t)]
    · have := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right h1 ht)
      linarith [Real.exp_pos (b * t)]
  calc Real.exp (x * s) = Real.exp (x * (s - t)) * Real.exp (x * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := mul_le_mul (Real.exp_le_exp.2 h3) h4 (Real.exp_pos _).le (Real.exp_pos _).le

theorem summable_along {G G' : Type} [Group G] [Group G'] [TopologicalSpace G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' K' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (η : G' → ℝ) (hη : IsHt Γ' K' P' η) (x : ℝ)
    (hc : Conv Γ' P' fun g => x * η g) : Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := by
  let T : G' → ℂ := fun y => (Real.exp (x * η y) : ℂ)
  have hT : GlobalTheory.AutomorphicL2Unitary.LeftInv (P' ⊓ Γ') T := fun γ hγ y => by
    simp only [T, hη.left γ hγ.1 y, hη.rat γ hγ.2 hγ.1, zero_add]
  obtain ⟨-, h⟩ := GlobalTheory.StdUnn.cosetSum_along_mulEquiv G G' Φ P Γ P' Γ' hP hΓ T 1 1 (fun g => T (Φ g))
    (fun g => by simp) hT
  have h1 : GlobalTheory.Eis.CosetConv P' Γ' T (Φ (1 * 1)) := by
    refine (hc (Φ (1 * 1))).congr fun q => ?_
    show _ = ‖((Real.exp (x * η (rep q * Φ (1 * 1))) : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine ((h 1).1 h1).congr fun q => ?_
  show ‖((Real.exp (x * η (Φ (rep q * 1))) : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_one]

theorem bounded_of_law {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (Φ : G ≃ₜ* G')
    (P : Subgroup G) (Γ' K' P' : Subgroup G') (c : G' → ℂ) (hK : IsCompact (K' : Set G')) (hPar : IsPar Γ' K' P' c)
    (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (f : G → ℂ) (hf : Continuous f) (hlaw : ∀ q ∈ P, ∀ g, f (q * g) = c (Φ q) * f g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image Φ.symm.continuous).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  obtain ⟨p, hp, k, hk, e⟩ := hPar.iwa (Φ x)
  have hx : x = Φ.symm p * Φ.symm k := by
    apply Φ.injective
    simp [e]
  have hq : Φ.symm p ∈ P := (hP _).2 (by simpa using hp)
  rw [hx, hlaw _ hq, Φ.apply_symm_apply, norm_mul, hPar.ch.norm p hp, one_mul]
  exact (hM _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)

theorem eFar : EFar := by
  intro hLip G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η R hK hPar hη hΓ hP hcv f hf hlaw
  have hsum : ∀ x : ℝ, R < x → Summable fun q : Cos P Γ => Real.exp (x * η (Φ (rep q))) := fun x hx =>
    summable_along Φ.toMulEquiv Γ P Γ' K' P' hΓ hP η hη x (hcv x hx)
  obtain ⟨M, hM0, hM⟩ := bounded_of_law Φ P Γ' K' P' c hK hPar hP f hf hlaw
  have key : ∀ a b : ℝ, R < a → R < b → ∀ C : Set G, IsCompact C → ∃ u : Cos P Γ → ℝ, Summable u ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ g ∈ C, ∀ q : Cos P Γ,
        ‖Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g)‖ ≤ u q := by
    intro a b ha hb C hC
    obtain ⟨L, hL⟩ := hLip G' Γ' K' P' η hK hPar.iwa hη (Φ '' C) (hC.image Φ.continuous)
    refine ⟨fun q => M * Real.exp ((|a| + |b|) * L) *
      (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q)))), ((hsum a ha).add (hsum b hb)).mul_left _, ?_⟩
    intro z h1 h2 g hg q
    have h3 := exp_mul_le (s := η (Φ (rep q * g))) (t := η (Φ (rep q))) (L := L) h1 h2
      (by rw [map_mul]; exact hL _ _ ⟨g, hg, rfl⟩)
    have h4 : (z * (η (Φ (rep q * g)) : ℂ)).re = z.re * η (Φ (rep q * g)) := by simp
    rw [norm_mul, Complex.norm_exp, h4]
    calc _ ≤ (Real.exp ((|a| + |b|) * L) * (Real.exp (a * η (Φ (rep q))) + Real.exp (b * η (Φ (rep q))))) * M :=
          mul_le_mul h3 (hM _) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcont : ∀ q : Cos P Γ, Continuous fun y : ℂ × G =>
      Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2) := fun q => by
    have h1 : Continuous fun y : ℂ × G => rep q * y.2 := continuous_const.mul continuous_snd
    have h2 : Continuous fun y : ℂ × G => ((η (Φ (rep q * y.2)) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hη.cont.comp (Φ.continuous.comp h1))
    exact (Complex.continuous_exp.comp (continuous_fst.mul h2)).mul (hf.comp h1)
  have hopen : ∀ a b : ℝ, IsOpen {z : ℂ | a < z.re ∧ z.re < b} := fun a b =>
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hab : ∀ z : ℂ, R < z.re → R < (R + z.re) / 2 ∧ R < z.re + 1 ∧ z ∈ {w : ℂ | (R + z.re) / 2 < w.re ∧ w.re < z.re + 1} :=
    fun z hz => ⟨by linarith, by linarith, by show _ ∧ _; constructor <;> linarith⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz C hC
    obtain ⟨u, hu, hb⟩ := key z.re z.re hz hz C hC
    exact ⟨u, hu, fun g hg q => hb z le_rfl le_rfl g hg q⟩
  · intro g z₀ hz₀
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 {g} isCompact_singleton
    have hd : DifferentiableOn ℂ (fun z => ∑' q : Cos P Γ, Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g))
        {w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} := by
      refine Complex.differentiableOn_tsum_of_summable_norm hu (fun q => ?_) (hopen _ _)
        (fun q w hw => hb w hw.1.le hw.2.le g rfl q)
      have : Differentiable ℂ fun z : ℂ => Complex.exp (z * η (Φ (rep q * g))) * f (rep q * g) := by fun_prop
      exact this.differentiableOn
    exact (hd.differentiableAt ((hopen _ _).mem_nhds h3)).differentiableWithinAt
  · rintro ⟨z₀, g₀⟩ ⟨hz₀, -⟩
    obtain ⟨h1, h2, h3⟩ := hab z₀ hz₀
    obtain ⟨C', hC'c, hC'm⟩ := exists_compact_mem_nhds (Φ g₀)
    have hCm : Φ.symm '' C' ∈ 𝓝 g₀ := Filter.mem_of_superset (Φ.continuous.continuousAt.preimage_mem_nhds hC'm)
      fun x hx => ⟨Φ x, hx, by simp⟩
    obtain ⟨u, hu, hb⟩ := key _ _ h1 h2 _ (hC'c.image Φ.symm.continuous)
    have hd : ContinuousOn (fun y : ℂ × G => ∑' q : Cos P Γ, Complex.exp (y.1 * η (Φ (rep q * y.2))) * f (rep q * y.2))
        ({w : ℂ | (R + z₀.re) / 2 < w.re ∧ w.re < z₀.re + 1} ×ˢ (Φ.symm '' C')) :=
      continuousOn_tsum (fun q => (hcont q).continuousOn) hu
        fun q y hy => hb y.1 hy.1.1.le hy.1.2.le y.2 hy.2 q
    exact (hd.continuousAt (prod_mem_nhds ((hopen _ _).mem_nhds h3) hCm)).continuousWithinAt
  · intro z γ hγ g
    refine GlobalTheory.Eis.leftInv_cosetSum (fun δ hδ x => ?_) γ hγ g
    have h1 : Φ δ ∈ P' := (hP δ).1 hδ.1
    have h2 : Φ δ ∈ Γ' := (hΓ δ).1 hδ.2
    simp only [hlaw δ hδ.1 x, map_mul, hη.left _ h1, hη.rat _ h2 h1, hPar.ch.rat _ h2 h1, zero_add, one_mul]

end GlobalTheory.CompanionTheory.FarSeries

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinIwasawaEstimate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr PositivityTheory.Rg.SwEis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SwEisIwa

theorem iwa_of_rank (hC : Chart) (D : D7) (χ : (AE D)ˣ →* Circle) (V : HSp D) :
    Iwa ((adCM D.sp.cm.sig χ).uQ (-1) (Set.univ : Set (Fin V.rank))) ((adCM D.sp.cm.sig χ).uK (-1) (Fin V.rank)) := by
  obtain ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  obtain ⟨Φ, p, -, hQ, hK, -, -⟩ := hC D χ V a ha
  intro g
  obtain ⟨q, k, hk, hqk⟩ := (GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha)).1
    (Φ.symm g * (p : GA D (dblSp V))⁻¹)
  refine ⟨Φ ((q : GA D (dblSp V)) * p), (hQ _).1 (Subgroup.mul_mem _ q.2 p.2),
    Φ ((p : GA D (dblSp V))⁻¹ * k * p), (hK k).1 hk, ?_⟩
  have h1 : Φ.symm g = (q : GA D (dblSp V)) * k * p := by
    rw [← hqk, inv_mul_cancel_right]
  have h2 : (q : GA D (dblSp V)) * p * ((p : GA D (dblSp V))⁻¹ * k * p) = (q : GA D (dblSp V)) * k * p := by
    group
  rw [← map_mul, h2, ← h1]
  exact (Φ.apply_symm_apply g).symm

theorem eIwa : EIwa := fun hC D χ n =>
  iwa_of_rank hC D χ (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n)

end GlobalTheory.CompanionTheory.SwEisIwa

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalSmoothModuleStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_cuspidal_smooth_module : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ _root_.GlobalTheory.CuspRep.IsStable V := by
  first | exact @GlobalTheory.CompanionTheory.StableMod.exists_stable | exact GlobalTheory.CompanionTheory.StableMod.exists_stable | (intros; apply GlobalTheory.CompanionTheory.StableMod.exists_stable <;> assumption)
end

