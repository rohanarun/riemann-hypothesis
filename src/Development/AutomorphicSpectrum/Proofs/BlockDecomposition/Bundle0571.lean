module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorCompactUnipotentFixer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0431
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellJacquetMapSurjectiveWhittaker
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.OpenCoinv

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)

theorem translate_mem {n : GL (Fin N) k} (hn : n ∈ unipB k (Fin N)) {g : IndSp (stdBlocks d hd) ρ}
    (hg : g ∈ openFns d hd ρ) : parInd (stdBlocks d hd) ρ n g ∈ openFns d hd ρ := by
  intro x hx
  obtain ⟨p, hp, n', hn', e⟩ := hg (x * n) hx
  refine ⟨p, hp, n' * n⁻¹, mul_mem hn' (inv_mem hn), ?_⟩
  rw [← mul_assoc, ← e]
  group

theorem span_mem (J : openFns d hd ρ →ₗ[ℂ] W) (S : Submodule ℂ W) (X : Set (IndSp (stdBlocks d hd) ρ))
    (hX : ∀ x ∈ X, ∃ hx : x ∈ openFns d hd ρ, J ⟨x, hx⟩ ∈ S) {f : IndSp (stdBlocks d hd) ρ}
    (hf : f ∈ Submodule.span ℂ X) : ∃ hx : f ∈ openFns d hd ρ, J ⟨f, hx⟩ ∈ S := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hX x hx
  | zero =>
    refine ⟨zero_mem _, ?_⟩
    have e : J ⟨0, zero_mem _⟩ = 0 := map_zero J
    rw [e]
    exact S.zero_mem
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have e : J ⟨x + y, add_mem a b⟩ = J ⟨x, a⟩ + J ⟨y, b⟩ := (map_add J ⟨x, a⟩ ⟨y, b⟩)
    rw [e]
    exact add_mem ha hb
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨Submodule.smul_mem _ c a, ?_⟩
    have e : J ⟨c • x, Submodule.smul_mem _ c a⟩ = c • J ⟨x, a⟩ := (map_smul J c ⟨x, a⟩)
    rw [e]
    exact S.smul_mem c ha

theorem leviEmb_inj {x y : Levi k fun a => Fin (d a)}
    (e : leviEmb k (stdBlocks d hd) x = leviEmb k (stdBlocks d hd) y) : x = y := by
  funext a
  apply Units.ext
  ext i j
  have he := congrArg (fun g : GL (Fin N) k =>
    (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) e
  simpa only [leviEmb_apply_same] using he

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Rodier.OpenCoinv

namespace GlobalTheory.CompanionTheory.Rodier.OpenCoinv

set_option maxHeartbeats 2000000 in
theorem openFns_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ J : openFns d hd ρ →ₗ[ℂ] W, Function.Surjective J ∧ ∀ f : openFns d hd ρ, J f ∈ twKer ρ (unipM k d) (whitM d ψ) ↔ (f : IndSp (stdBlocks d hd) ρ) ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  obtain ⟨J, vol, hU, hL, hV⟩ := GlobalTheory.T.open_cell_jacquet_integral_volume k ψ hψ h N d hd ρ hρ
  obtain ⟨hfac, -⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad k h N d hd
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.open_cell_levi_unipotent_conjugation k ψ h N d hd
  obtain ⟨-, huniq, -⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd
  have hUB : unipU k d hd ≤ unipB k (Fin N) := inf_le_left
  have hLB : unipL k d hd ≤ unipB k (Fin N) := inf_le_left
  have surj : Function.Surjective J := by
    intro v
    obtain ⟨L₀, hL₀U, hc, hO, hθ, f, hf, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.OpenBump.exists_openFns_bump k ψ hψ h N d hd ρ hρ v
    obtain ⟨hpos, hJ⟩ := hV L₀ hL₀U hc hO
    have e := hJ ⟨f, hf⟩ v (fun u hb hu => by
      show f.1.1 (pm k (wOpen d hd) * u) = _
      rw [h1 u hu, hθ u hb hu]
      simp) h2
    refine ⟨((vol L₀ : ℂ))⁻¹ • ⟨f, hf⟩, ?_⟩
    have hne : (vol L₀ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [map_smul, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have gen : ∀ (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (g : openFns d hd ρ),
      ∃ hx : parInd (stdBlocks d hd) ρ n g.1 - ((whitChar ψ N ⟨n, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ,
        J ⟨_, hx⟩ ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro n hn g
    obtain ⟨a, ha, u, hu, rfl⟩ := hfac n hn
    have hub := hUB hu
    have hab := hLB ha
    obtain ⟨m, hm, hθm⟩ := hl1 a ha hab
    let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ u g.1, translate_mem d hd ρ hub g.2⟩
    let g2 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g1.1, translate_mem d hd ρ hab g1.2⟩
    have e1 : J g1 = ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • J g := hU u hu hub g g1 rfl
    have e2 : J g2 = ρ m.1 (J g1) := hL a ha m hm g1 g2 rfl
    have e3 : parInd (stdBlocks d hd) ρ (a * u) g.1 = g2.1 := by
      rw [map_mul]
      rfl
    have hθ : whitChar ψ N ⟨a * u, hn⟩ = whitChar ψ N ⟨a, hab⟩ * whitChar ψ N ⟨u, hub⟩ := by
      rw [← map_mul]
      rfl
    have hx : parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 ∈ openFns d hd ρ :=
      sub_mem (translate_mem d hd ρ hn g.2) (Submodule.smul_mem _ _ g.2)
    refine ⟨hx, ?_⟩
    have e4 : (⟨_, hx⟩ : openFns d hd ρ) = g2 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g :=
      Subtype.ext (by
        show parInd (stdBlocks d hd) ρ (a * u) g.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1 =
          g2.1 - ((whitChar ψ N ⟨a * u, hn⟩ : ℂˣ) : ℂ) • g.1
        rw [e3])
    rw [e4, map_sub, map_smul, e2, e1, map_smul, hθ, hθm, Units.val_mul]
    have e5 : ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • ρ m.1 (J g) -
        (((whitM d ψ m : ℂˣ) : ℂ) * ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ)) • J g =
        ((whitChar ψ N ⟨u, hub⟩ : ℂˣ) : ℂ) • (ρ m.1 (J g) - ((whitM d ψ m : ℂˣ) : ℂ) • J g) := by
      rw [smul_sub, smul_smul, mul_comm]
    rw [e5]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, J g, rfl⟩)
  have bwd : ∀ f : openFns d hd ρ, f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) →
      J f ∈ twKer ρ (unipM k d) (whitM d ψ) := by
    intro f hf
    have hs := _root_.GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer k ψ hψ h N d hd ρ (unipB k (Fin N)) le_rfl
      (fun s hs => GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N s hs) (whitChar ψ N)
      (fun q hq => rfl) f.1 f.2 hf
    obtain ⟨_, h2⟩ := span_mem d hd ρ J (twKer ρ (unipM k d) (whitM d ψ)) _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      exact gen q.1 q.2 ⟨g, hg⟩) hs
    exact h2
  have key : ∀ f : openFns d hd ρ, J f = 0 →
      f.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) := by
    intro f hf
    obtain ⟨L, hLU, hLc, hLO, hsupp⟩ := _root_.GlobalTheory.CompanionTheory.Rodier.exists_compact_open_support k h N d hd ρ hρ f.1 f.2
    have hLB' : L ≤ unipB k (Fin N) := hLU.trans hUB
    let θL : L →* ℂˣ := (whitChar ψ N).comp (Subgroup.inclusion hLB')
    have hopen : IsOpen (θL.ker : Set L) :=
      (GlobalTheory.Whittaker.isSmoothChar_whitChar (N := N) hψ).preimage (f := Subgroup.inclusion hLB') (continuous_subtype_val.subtype_mk fun x => hLB' x.2)
    obtain ⟨f', hd1, hd2, hd3⟩ := GlobalTheory.T.projection_to_twisted_eigenfunction_support _ _ L hLc θL hopen f.1
    have hsupp' : ∀ g, f'.1.1 g ≠ 0 → ∃ p ∈ parab k (stdBlocks d hd), ∃ u ∈ L, g = p * pm k (wOpen d hd) * u := by
      intro g hg
      obtain ⟨l, hl, hne⟩ := hd2 g hg
      obtain ⟨p, hp, u, hu, e⟩ := hsupp _ hne
      refine ⟨p, hp, u * l⁻¹, mul_mem hu (inv_mem hl), ?_⟩
      rw [← mul_assoc, ← e]
      group
    have hf'o : f' ∈ openFns d hd ρ := fun g hg => by
      obtain ⟨p, hp, u, hu, e⟩ := hsupp' g hg
      exact ⟨p, hp, u, hLB' hu, e⟩
    have hdiff := _root_.GlobalTheory.CompanionTheory.Rodier.OpenExact.mem_span_openFns_of_mem_twKer k ψ hψ h N d hd ρ L hLB' (fun s hs => ⟨L, le_rfl, hs, hLc⟩) θL
      (fun q hq => rfl) (f.1 - f') (sub_mem f.2 hf'o) hd1
    obtain ⟨hx, hJ0⟩ := span_mem d hd ρ J ⊥ _ (by
      rintro _ ⟨q, g, hg, rfl⟩
      have hqb := hLB' q.2
      have hx : parInd (stdBlocks d hd) ρ q.1 g - ((θL q : ℂˣ) : ℂ) • g ∈ openFns d hd ρ :=
        sub_mem (translate_mem d hd ρ hqb hg) (Submodule.smul_mem _ _ hg)
      refine ⟨hx, ?_⟩
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ q.1 g, translate_mem d hd ρ hqb hg⟩
      have e1 : J g1 = ((whitChar ψ N ⟨q.1, hqb⟩ : ℂˣ) : ℂ) • J ⟨g, hg⟩ := hU q.1 (hLU q.2) hqb ⟨g, hg⟩ g1 rfl
      have e2 : (⟨_, hx⟩ : openFns d hd ρ) = g1 - ((θL q : ℂˣ) : ℂ) • ⟨g, hg⟩ := rfl
      rw [e2, map_sub, map_smul, e1]
      exact (sub_self _ : _ = (0 : W))) hdiff
    let F' : openFns d hd ρ := ⟨f', hf'o⟩
    have hJF : J F' = 0 := by
      have e : (⟨_, hx⟩ : openFns d hd ρ) = f - F' := rfl
      rw [e, map_sub, hf] at hJ0
      simpa using hJ0
    obtain ⟨hpos, hJ⟩ := hV L hLU hLc hLO
    have hv := hJ F' (f'.1.1 (pm k (wOpen d hd))) (fun u hb hu => hd3 ⟨u, hu⟩ _) (fun u hu hnot => by
      by_contra hne
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' _ hne
      exact hnot (huniq p hp l (hLU hl) u hu e.symm ▸ hl))
    have hne : (vol L : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hv0 : f'.1.1 (pm k (wOpen d hd)) = 0 := by
      rw [hJF] at hv
      exact (smul_eq_zero.1 hv.symm).resolve_left hne
    have hf0 : f' = 0 := by
      refine Subtype.ext (Subtype.ext (funext fun g => ?_))
      by_contra hg
      obtain ⟨p, hp, l, hl, e⟩ := hsupp' g hg
      apply hg
      have h1 := f'.1.2 ⟨p, hp⟩ (pm k (wOpen d hd))
      rw [hv0, map_zero] at h1
      rw [e]
      have h2 := hd3 ⟨l, hl⟩ (p * pm k (wOpen d hd))
      rw [show f'.1.1 (p * pm k (wOpen d hd)) = 0 from h1, smul_zero] at h2
      exact h2
    rw [hf0, sub_zero] at hd1
    refine (Submodule.span_le.2 ?_ : twKer (parInd (stdBlocks d hd) ρ) L θL ≤ _) hd1
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨⟨n.1, hLB' n.2⟩, v, rfl⟩
  have lift : ∀ s ∈ twKer ρ (unipM k d) (whitM d ψ), ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s := by
    intro s hs
    refine Submodule.span_induction (p := fun s _ => ∃ F : openFns d hd ρ,
      F.1 ∈ twKer (parInd (stdBlocks d hd) ρ) (unipB k (Fin N)) (whitChar ψ N) ∧ J F = s) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨m, v, rfl⟩
      obtain ⟨g, rfl⟩ := surj v
      obtain ⟨a, ha, hm⟩ := hl2 m
      have hab := hLB ha
      obtain ⟨m', hm', hθ⟩ := hl1 a ha hab
      have hmm : m = m' := Subtype.ext (leviEmb_inj d hd (hm.symm.trans hm'))
      rw [← hmm] at hθ
      let g1 : openFns d hd ρ := ⟨parInd (stdBlocks d hd) ρ a g.1, translate_mem d hd ρ hab g.2⟩
      refine ⟨g1 - ((whitChar ψ N ⟨a, hab⟩ : ℂˣ) : ℂ) • g, Submodule.subset_span ⟨⟨a, hab⟩, g.1, rfl⟩, ?_⟩
      rw [map_sub, map_smul, hL a ha m hm g g1 rfl, hθ]
    · exact ⟨0, zero_mem _, map_zero J⟩
    · rintro x y _ _ ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩
      exact ⟨F + F', add_mem hF hF', map_add J F F'⟩
    · rintro c x _ ⟨F, hF, rfl⟩
      exact ⟨c • F, Submodule.smul_mem _ c hF, map_smul J c F⟩
  refine ⟨J, surj, fun f => ⟨fun hf => ?_, bwd f⟩⟩
  obtain ⟨F, hF, e⟩ := lift _ hf
  have h0 := key (f - F) (by rw [map_sub, e, sub_self])
  have h1 : (f : IndSp (stdBlocks d hd) ρ) = (f - F).1 + F.1 := by
    show (f : IndSp (stdBlocks d hd) ρ) = (f.1 - F.1) + F.1
    rw [sub_add_cancel]
  rw [h1]
  exact add_mem h0 hF

end GlobalTheory.CompanionTheory.Rodier.OpenCoinv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitIntegralInvariantE0
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {K : Type} [CommRing K] {M : ℕ}

def lowerB (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => U i.succ.succ j.succ.succ

theorem col_zero {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K}
    (h : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0) (i : Fin (M + 2)) :
    U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i := by
  have := congrFun h i
  rw [← this]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem row_one (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) (j : Fin M) :
    U 1 j.succ.succ = 0 := by
  have h := congrFun (congrFun hU 0) j.succ.succ
  have h1 : U 1 0 = 0 := h0 1
  have hr : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h
  simpa [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h0 0, h1, hr] using h

theorem lowerB_isometry (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) :
    cT s (lowerB U) * A * lowerB U = A := by
  ext i j
  have h := congrFun (congrFun hU i.succ.succ) j.succ.succ
  have h1 : ∀ j : Fin M, U 1 j.succ.succ = 0 := row_one s A hU h0
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h ⊢
  simpa [lowerB, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h1] using h

theorem mulVec_cons (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : K) (Y : Fin M → K) :
    U.mulVec (Fin.cons a (Fin.cons 0 Y)) =
      Fin.cons (a + ∑ i, U 0 i.succ.succ * Y i) (Fin.cons 0 ((lowerB U).mulVec Y)) := by
  have e1 : U 1 0 = 0 := h0 1
  have er : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  have e0 : U 0 0 = 1 := h0 0
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e0]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e1, h1]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, er, lowerB]

theorem mulVec_consA {n : ℕ} (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (hfix : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    (fun k => U.mulVec (consA a Y k)) =
      consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (fun j => (lowerB U).mulVec (Y j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simpa [consA] using hfix
  · simpa [consA] using mulVec_cons U h0 h1 (a 0 j) (Y j)

theorem map_hypOne {L : Type} [CommRing L] (f : K →+* L) (A : Matrix (Fin M) (Fin M) K) :
    (hypOne A).map f = hypOne (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_hypOne (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) :=
  map_hypOne (inclR R) J

theorem exists_HA (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : J.det ≠ 0) {κ : Matrix (Fin M) (Fin M) (R ⊗[F] E)}
    (hκ : cT (sigR R σ) κ * JR (F := F) R J * κ = JR (F := F) R J) :
    ∃ h : HA R σ J, ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = κ := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hi : (J⁻¹).map (inclR (F := F) R) * JR (F := F) R J = 1 := by
    have h1 := congrArg (fun A : Matrix (Fin M) (Fin M) E => A.map (inclR (F := F) R)) (Matrix.nonsing_inv_mul J hu)
    simpa [JR, Matrix.map_mul, Matrix.map_one] using h1
  have hl : ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ = 1 := by
    calc ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ
        = (J⁻¹).map (inclR (F := F) R) * (cT (sigR R σ) κ * JR (F := F) R J * κ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hκ, hi]
  have hr := mul_eq_one_comm.mp hl
  let G : GL (Fin M) (R ⊗[F] E) := ⟨κ, _, hr, hl⟩
  have hG : G ∈ HR R σ J := hκ
  exact ⟨(⟨G, hG⟩ : HR R σ J), rfl⟩

end Main

theorem stageInt_eq_of_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₀ : Measure (Fin n → Fin M → R ⊗[F] E), (∀ h : HA R σ J, m₀.map (actW R σ J h) = m₀) → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ g g' : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = actW R σ (hypOne J) g' (e0 _ M) → stageInt R σ J b lam m₀ φ g = stageInt R σ J b lam m₀ φ g' := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ _ _ _ hL n d b lam hlam m₀ hm₀ φ hφ g g' hgg
  haveI : IsTopologicalRing R := hL.1
  haveI : LocallyCompactSpace R := hL.2.1
  haveI : SecondCountableTopology R := hL.2.2.1
  haveI : T2Space R := hL.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  haveI : BorelSpace (Fin 1 → Fin n → R ⊗[F] E) := tK8 1 n
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := tK8 (n + 1) (M + 2)
  obtain ⟨-, hW, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R d b lam hlam
  haveI := hW 1 n
  obtain ⟨-, -, -, -, -, hA⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R
  obtain ⟨-, -, -, -, -, hA'⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm M J hJ R
  obtain ⟨-, e1, em, -⟩ := hA 1
  obtain ⟨hc, -, hm, -⟩ := hA (n + 1)
  obtain ⟨hc', -, -, -⟩ := hA' n

  set u : HA R σ (hypOne J) := g⁻¹ * g' with hu_def
  have hg' : g' = g * u := by simp [hu_def]
  have hfix : actW R σ (hypOne J) u (e0 _ M) = e0 _ M := by
    rw [hu_def, em, ← hgg, ← em, inv_mul_cancel, e1]
  set U : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E) :=
    (HA.mat R σ (hypOne J) u).val with hU_def
  have hfixV : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0 := congrFun hfix 0
  have h0 := col_zero hfixV
  have hUu : cT (sigR R σ) U * hypOne (JR (F := F) R J) * U = hypOne (JR (F := F) R J) := by
    rw [← JR_hypOne]
    exact (show HR R σ (hypOne J) from u).2
  have h1 := row_one _ _ hUu h0
  obtain ⟨k, hk⟩ := exists_HA R σ hJ.2 (lowerB_isometry _ _ hUu h0)

  have hact : ∀ (a : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E),
      actW R σ (hypOne J) u (consA a Y) =
        consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y) := by
    intro a Y
    have := mulVec_consA U hfixV h0 h1 a Y
    have e : actW R σ J k Y = fun j => (lowerB U).mulVec (Y j) := by
      funext j
      simp only [actW, actTup, hk]
    rw [e, ← this]
    rfl

  let G : (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ := fun Y =>
    ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n)
  have hcons : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
      (consA p.2 p.1 : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := by
    refine continuous_pi fun k => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) k
    · refine Fin.cases ?_ (fun i => ?_) i <;> simpa [consA] using continuous_const
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simp only [consA, Fin.cons_succ, Fin.cons_zero]
        fun_prop
      · simpa [consA] using continuous_const
      · simp only [consA, Fin.cons_succ]
        fun_prop
  have hGm : Measurable G := by
    have hf : Measurable fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        φ (actW R σ (hypOne J) g (consA p.2 p.1)) :=
      hφ.comp (hc.comp (continuous_const.prodMk hcons)).measurable
    exact hf.lintegral_prod_right'
  have hkm : Measurable (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) :=
    (hc'.comp (continuous_const.prodMk continuous_id)).measurable
  have hinner : ∀ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) =
      G (actW R σ J k Y) := by
    intro Y
    have : ∀ a, actW R σ (hypOne J) g' (consA a Y) =
        actW R σ (hypOne J) g (consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y)) := by
      intro a
      rw [hg', hm, hact]
    simp only [this]
    exact lintegral_add_right_eq_self
      (fun a => φ (actW R σ (hypOne J) g (consA a (actW R σ J k Y)))) _
  show (∫⁻ Y, G Y ∂m₀) = ∫⁻ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) ∂m₀
  simp only [hinner]
  rw [← lintegral_map hGm hkm, hm₀ k]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariant
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem nuT_shear_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t),
    (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ y
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) t n
  obtain ⟨k1, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hQ := sigmaFinite_parameter_product_measure I μ hμ
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have hS : Measurable fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y) :=
    (continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))).measurable
  have hτ : MeasurePreserving (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y))
      (I.νK.prod (Q0 I μ)) (I.νK.prod (Q0 I μ)) := by
    unfold Q0
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
      ((MeasurePreserving.id _).prod (measurePreserving_add_right μ y)))
  have hπ := measurable_pi (d := d) hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)) ∘
        (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y)) := by
    funext p
    refine Prod.ext rfl ?_
    have key : ∀ {a b c : ℕ} (g : Mx D a a) (ξ : Mx D a b) (u : Mx D a c) (y' y : Mx D b c),
        mm g (mm ξ y' + u) + mm (mm g ξ) y = mm g (mm ξ (y' + y) + u) := by
      intro a b c g ξ u y' y
      simp only [mm, Matrix.mul_add, Matrix.mul_assoc]
      abel
    exact key _ _ _ _ _
  unfold nuT
  rw [Measure.map_map hS hπ, hcomp, ← Measure.map_map hπ hτ.measurable, hτ.map_eq]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

