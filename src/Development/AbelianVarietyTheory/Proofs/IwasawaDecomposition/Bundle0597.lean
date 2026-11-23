module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUnifor
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh

theorem exists_comb_of_exp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {x x' : Sp ℂ ⟶ Z.X} (hxx : x' = x) {g : ℕ} (ex : (Fin g → ℂ) → (Over.mk x' ⟶ Z.t.G))
    (hex : IsExpAt Z.t x' ex) (f : EigFrame Z σ x) (τ : E →+* ℂ) (δ : Fin (Dw.mult τ) → Fin g → ℂ)
    (hδ : ∀ b, IsDerivAt0 (fun z => (ex z).left) (δ b) (f.v τ b)) (v' : Sp (DualNumber ℂ) ⟶ Z.t.G.left)
    (hv' : IsTanAtG Z.t x v') (heig : ∀ a, v' ≫ (Z.t.act.act a).left = spMap (epsMul (σ (embK c τ a))) ≫ v')
    (w : Fin g → ℂ) (hw : IsDerivAt0 (fun z => (ex z).left) w v') :
    ∃ a : Fin (Dw.mult τ) → ℂ, IsCombAtG Z.t x (f.v τ) a v' ∧ w = ∑ b, a b • δ b := by
  subst hxx
  obtain ⟨a, ha, -⟩ := f.basis τ v' hv' heig
  have e1 : ex 0 = 1 := by
    have h := hex.1 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hd := GlobalTheory.ShFam.Hor.ExpDirs.isDerivAt0_of_comb (congrArg (·.left) e1) (f.tan τ) hδ hv' ha
  obtain ⟨w', -, hu⟩ := hex.2.2 v' hv'
  exact ⟨a, ha, (hu w hw).trans (hu _ hd).symm⟩

end GlobalTheory.HolCoordEv

namespace GlobalTheory.HolCoordEv

open GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom)

theorem coords_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hg hU d u₀ R _ φR xR fR ev k G τ hev hG hφ hpt
  classical
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hP⟩ := hU
  choose Pm h1 h2 h3 h4 _ using hP
  obtain ⟨h₀, -⟩ := hpt.self_of_nhds
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let x : (Fin d → ℂ) → (U.X k).dom := fun b =>
    if h : G (L.symm b) ∈ (U.X k).dom then ⟨G (L.symm b), h⟩ else ⟨G u₀, h₀⟩
  have hxb : ∀ b (h : G (L.symm b) ∈ (U.X k).dom), x b = ⟨G (L.symm b), h⟩ := fun b h => dif_pos h
  let P : (Fin d → ℂ) → ((F.Di (ik k)).La →+ (Fin g → ℂ)) := fun b => Pm k (x b)
  let p : (Fin d → ℂ) → (Sp ℂ ⟶ Xo.XF c) := fun b => GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k (x b))
  have hu : ∀ b, F.u (ik k) (P b) =
      p b ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    fun b => (h3 k (x b)).symm.trans (ptF_fst (U.un k (x b))).symm
  have hs : ∀ b, p b ≫ pullback.snd _ _ = spMap σ := fun b => ptF_snd (U.un k (x b))
  have hgood : ∀ᶠ u in 𝓝 u₀, G u ∈ (U.X k).dom ∧
      ∀ τ' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    (hpt.mono fun u hu => hu.1).and
      (eventually_all.2 fun τ' => eventually_all.2 fun a => eventually_all.2 fun b => hG τ' a b)
  obtain ⟨B₀, hB₀, hB₀o, hu₀⟩ := eventually_nhds_iff.1 hgood
  let B : Set (Fin d → ℂ) := L.symm ⁻¹' B₀
  have hBo : IsOpen B := hB₀o.preimage L.symm.continuous
  have hb₀ : L u₀ ∈ B := by
    show L.symm (L u₀) ∈ B₀
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hu₀
  have hPd : ∀ a, DifferentiableOn ℂ (fun b => P b a) B := fun a => differentiableOn_pi.2 fun j =>
    (TrueCx.TorHolo.differentiableOn_perFr (U.X k) (x := fun b => G (L.symm b)) (fun b hb => (hB₀ _ hb).1)
      (fun τ' a' c' b hb => (((hB₀ _ hb).2 τ' a' c').comp b L.symm.differentiableAt).differentiableWithinAt)
      _ _ _).congr fun b hb => by
        show Pm k (x b) a j = _
        rw [h1, hxb b (hB₀ _ hb).1]
  let ev' : (Fin d → ℂ) → (R →+* ℂ) := fun b => ev (L.symm b)
  let Ex : (Fin d → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun b z =>
    liftEx Z F (p b) (ik k) (P b) (hu b) z ≫ Z.m.φ
  let Wd : Fin (Dw.mult τ) → (Fin d → ℂ) → Fin g → ℂ := fun i b =>
    if h : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) then h.choose else 0
  have core : ∀ b (h : G (L.symm b) ∈ (U.X k).dom),
      (cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z = spMap (ev (L.symm b)) ≫ xR →
      (ev (L.symm b)).comp φR = σ → ∀ i,
      IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) ∧
      IsCombAtG Z.t ((cxPt Z (U.un k ⟨G (L.symm b), h⟩)).1 ≫ genι Z)
        ((cxFrame Z (U.un k ⟨G (L.symm b), h⟩)).v τ) (fun a => Wd i b (e.symm ⟨τ, a⟩))
        (spMap (dualMap (ev (L.symm b))) ≫ fR.v τ i) := by
    intro b h hx hφb i
    rw [← hxb b h] at hx ⊢
    obtain ⟨gF, hgF⟩ := HolFrames.exists_bc fR (ev (L.symm b)) (φ' := σ) hφb.symm hx
    have hxp : p b ≫ Z.jQ ≫ genι Z = (cxPt Z (U.un k (x b))).1 ≫ genι Z := (Category.assoc _ _ _).symm
    have hExp := isExpAt_pushEx E H Dw l Xo c O β Z g _ _ F (p b) (ik k) (P b) _ (hu b) rfl (h2 k (x b))
    have hδ : ∀ a, IsDerivAt0 (fun z => (pushEx Z F (p b) (ik k) (P b) _ (hu b) rfl z).left)
        (Pi.single (e.symm ⟨τ, a⟩) 1) ((cxFrame Z (U.un k (x b))).v τ a) := by
      intro a
      obtain ⟨w, hwt, hw0, hwm⟩ := EigFrame.ofFrPt_v Z (U.un k (x b))
        (x := (cxPt Z (U.un k (x b))).1 ≫ genι Z) (Category.assoc _ _ _).symm τ a
      have hw0' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m0.toSABMap.φ = (U.un k (x b)).u τ a := hw0
      have hwm' : (w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left) ≫ Z.m.φ = (cxFrame Z (U.un k (x b))).v τ a := hwm
      have hd : IsDerivAt0 (fun z => (F.ex (ik k) (P b) z).left) (Pi.single (e.symm ⟨τ, a⟩) 1)
          (w ≫ Z.m0.toSABMap.φ) := by
        exact (congrArg (IsDerivAt0 _ _) hw0').mpr (h4 k (x b) τ a)
      have := isDerivAt0_comp_hom (isDerivAt0_liftEx Z F (p b) (ik k) (P b) (h2 k (x b)) (hu b) hwt.1 hd) Z.m.φ
      exact (congrArg (IsDerivAt0 _ _) hwm').mp this
    have ht : IsTanAtG Z.t (p b ≫ Z.jQ ≫ genι Z) (gF.v τ i) := by
      rw [hxp]; exact gF.tan τ i
    have hex : ∃ w, IsDerivAt0 (Ex b) w (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      obtain ⟨w, hw, -⟩ := hExp.2.2 _ ht
      exact ⟨w, (hgF τ i) ▸ hw⟩
    have hW : IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      have e0 : Wd i b = hex.choose := dif_pos hex
      rw [e0]
      exact hex.choose_spec
    refine ⟨hW, ?_⟩
    obtain ⟨a, ha, hwa⟩ := exists_comb_of_exp hxp _ hExp (cxFrame Z (U.un k (x b))) τ _ hδ (gF.v τ i)
      (gF.tan τ i) (gF.eig τ i) (Wd i b) ((hgF τ i).symm ▸ hW)
    have hfa : (fun a' => Wd i b (e.symm ⟨τ, a'⟩)) = a := by
      funext a'
      rw [hwa]
      have hi : ∀ j j' : Fin (Dw.mult τ), e.symm ⟨τ, j⟩ = e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
      simp [Finset.sum_apply, Pi.single_apply, hi]
    rw [hfa, ← hgF τ i]
    exact ha
  have ht : Tendsto L.symm (𝓝 (L u₀)) (𝓝 u₀) := by
    simpa using L.symm.continuous.tendsto (L u₀)
  refine ⟨fun u a i => Wd i (L u) (e.symm ⟨τ, a⟩), fun a i => ?_, ?_⟩
  · have hev'' : ∀ t, ∀ᶠ b in 𝓝 (L u₀), DifferentiableAt ℂ (fun b => ev' b t) b := fun t => by
      filter_upwards [ht.eventually (hev t)] with b hb
      exact hb.comp b L.symm.differentiableAt
    have hW : ∀ᶠ b in 𝓝 (L u₀), IsDerivAt0 (Ex b) (Wd i b) (spMap (dualMap (ev' b)) ≫ fR.v τ i) := by
      filter_upwards [ht.eventually hpt, ht.eventually hφ] with b ⟨h, hx⟩ hφb
      exact (core b h hx hφb i).1
    have hd := eventually_differentiableAt_dir Z σ F (ik k) hBo hu (fun b => h2 k (x b)) hPd hs (fR.v τ i) ev' hb₀
      hev'' (Wd i) hW
    filter_upwards [(L.continuous.tendsto u₀).eventually hd] with u hu
    exact (differentiableAt_pi.1 hu (e.symm ⟨τ, a⟩)).comp u L.differentiableAt
  · filter_upwards [hpt, hφ] with u ⟨h, hx⟩ hφu
    refine ⟨h, fun i => ?_⟩
    have c := core (L u)
    rw [ContinuousLinearEquiv.symm_apply_apply] at c
    exact (c h hx hφu i).2

end GlobalTheory.HolCoordEv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.associated_psi_coordinates_of_tau_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W) (hg : Function.Injective g)
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
    (∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W)) →
    ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  first | exact @GlobalTheory.PsiFromTau.associated_of_tau | exact GlobalTheory.PsiFromTau.associated_of_tau | (intros; apply GlobalTheory.PsiFromTau.associated_of_tau <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedEntriesBoundedSiegelReduced
section
noncomputable section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem term_le_double_sum {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ p q, 0 ≤ f p q) (p q : Fin n) :
    f p q ≤ ∑ p, ∑ q, f p q := by
  calc f p q ≤ ∑ q, f p q := Finset.single_le_sum (fun q _ => hf p q) (Finset.mem_univ q)
    _ ≤ ∑ p, ∑ q, f p q := Finset.single_le_sum (f := fun p => ∑ q, f p q)
        (fun p _ => Finset.sum_nonneg fun q _ => hf p q) (Finset.mem_univ p)

theorem step_chain {n : ℕ} {d : Fin n → ℝ} (hs : ∀ p q : Fin n, (q : ℕ) = p + 1 → d p ≤ 4 * d q)
    (q : Fin n) : ∀ m (hm : (q : ℕ) + m < n), d q ≤ 4 ^ m * d ⟨q + m, hm⟩ := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hs ⟨q + m, by omega⟩ ⟨q + (m + 1), hm⟩ (by simp; omega)
    calc d q ≤ 4 ^ m * d ⟨q + m, by omega⟩ := h1
      _ ≤ 4 ^ m * (4 * d ⟨q + (m + 1), hm⟩) := by gcongr
      _ = 4 ^ (m + 1) * d ⟨q + (m + 1), hm⟩ := by ring

theorem gap_chain {n : ℕ} {d : Fin n → ℝ} {R : ℝ} (hR : 0 ≤ R) (p : Fin n) :
    ∀ m (hm : (p : ℕ) + m < n),
      (∀ k k' : Fin n, (k' : ℕ) = k + 1 → p ≤ k → (k' : ℕ) ≤ p + m → d k' ≤ R * d k) →
      d ⟨p + m, hm⟩ ≤ R ^ m * d p := by
  intro m
  induction m with
  | zero => intro hm _; simp
  | succ m ih =>
    intro hm h
    have h1 := ih (by omega) (fun k k' hk hpk hk' => h k k' hk hpk (by omega))
    have h2 := h ⟨p + m, by omega⟩ ⟨p + (m + 1), hm⟩ (by simp; omega)
      (by simp [Fin.le_def]) (by simp)
    calc d ⟨p + (m + 1), hm⟩ ≤ R * d ⟨p + m, by omega⟩ := h2
      _ ≤ R * (R ^ m * d p) := by gcongr
      _ = R ^ (m + 1) * d p := by ring

theorem balanced_entries_bounded : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) →
    (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) →
    (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  intro n K
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.siegel_unipotent_inv_bounded n
  obtain ⟨R, hR1, hR⟩ := _root_.GlobalTheory.SiegelGap.lowerBlock_eq_zero_of_gap n K c
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have hRn : (1 : ℝ) ≤ R ^ n := one_le_pow₀ hR1
  have hB : 0 ≤ 4 ^ n * R ^ n * max K 0 := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) hK0
  refine ⟨(n : ℝ) ^ 2 * |c| * (1 + 4 ^ n * R ^ n * max K 0), ?_⟩
  intro A A' d u hS hd hbal htr i j
  obtain ⟨v, hvu, huv, hvl, hvc⟩ := hc u hS.diag hS.lower hS.upper
  obtain ⟨hsym, hsum, hsum'⟩ := _root_.GlobalTheory.RedTh.adjoint_weighted_sq_trace n A A' d u v hd hvu huv hbal
  have hK' : ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum']; exact htr
  have hK : ∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 ≤ K := by
    rw [hsum]; exact htr
  set Ar := A.map (Int.cast : ℤ → ℝ) with hAr
  set W := u * Ar * v with hWdef
  set B := 4 ^ n * R ^ n * max K 0 with hBdef
  have hterm : ∀ p q, d p / d q * W p q ^ 2 ≤ max K 0 := fun p q =>
    (term_le_double_sum (fun p q => d p / d q * W p q ^ 2)
      (fun p q => mul_nonneg (div_nonneg (hd p).le (hd q).le) (sq_nonneg _)) p q).trans
      (hK.trans (le_max_left _ _))
  have hsq : ∀ p q, W p q ^ 2 ≤ d q / d p * max K 0 := by
    intro p q
    have hp := (hd p).ne'
    have hq := (hd q).ne'
    have e : W p q ^ 2 = d q / d p * (d p / d q * W p q ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hterm p q) (div_nonneg (hd q).le (hd p).le)
  have hW : ∀ p q, W p q ^ 2 ≤ B := by
    intro p q
    rcases le_or_gt q p with hqp | hpq
    · have hqp' : (q : ℕ) ≤ p := hqp
      have hm : (q : ℕ) + ((p : ℕ) - q) < n := by omega
      have h1 := step_chain hS.step q ((p : ℕ) - q) hm
      have hpe : (⟨(q : ℕ) + ((p : ℕ) - q), hm⟩ : Fin n) = p := by ext; simp; omega
      rw [hpe] at h1
      have h2 : (4 : ℝ) ^ ((p : ℕ) - q) ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : d q ≤ 4 ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
      have h5 : d q / d p ≤ 4 ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
      calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
        _ ≤ 4 ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
        _ ≤ 4 ^ n * max K 0 * R ^ n := le_mul_of_one_le_right (by positivity) hRn
        _ = B := by rw [hBdef]; ring
    · have hpq' : (p : ℕ) < q := hpq
      by_cases hgap : ∃ k k' : Fin n, (k' : ℕ) = k + 1 ∧ p ≤ k ∧ k' ≤ q ∧ R * d k < d k'
      · obtain ⟨k, k', hk, hpk, hkq, hlt⟩ := hgap
        have h0 : (u * A'.map (Int.cast : ℤ → ℝ) * v) q p = 0 :=
          hR A' d u v hS hd hvu huv hvl hvc hK' k k' hk hlt q p hpk hkq
        have h1 := hsym p q
        rw [h0, mul_zero] at h1
        have hz : W p q = 0 := by
          rcases mul_eq_zero.mp h1 with h | h
          · exact absurd h (hd p).ne'
          · exact h
        rw [hz]
        simpa using hB
      · push_neg at hgap
        have hm : (p : ℕ) + ((q : ℕ) - p) < n := by omega
        have h1 := gap_chain (d := d) (by linarith) p ((q : ℕ) - p) hm
          (fun k k' hk hpk hk' => hgap k k' hk hpk (by rw [Fin.le_def]; omega))
        have hqe : (⟨(p : ℕ) + ((q : ℕ) - p), hm⟩ : Fin n) = q := by ext; simp; omega
        rw [hqe] at h1
        have h2 : R ^ ((q : ℕ) - p) ≤ R ^ n := pow_le_pow_right₀ hR1 (by omega)
        have h3 : d q ≤ R ^ n * d p := h1.trans (mul_le_mul_of_nonneg_right h2 (hd p).le)
        have h5 : d q / d p ≤ R ^ n := by rw [div_le_iff₀ (hd p)]; exact h3
        calc W p q ^ 2 ≤ d q / d p * max K 0 := hsq p q
          _ ≤ R ^ n * max K 0 := mul_le_mul_of_nonneg_right h5 hK0
          _ ≤ 4 ^ n * (R ^ n * max K 0) := le_mul_of_one_le_left (by positivity) h4
          _ = B := by rw [hBdef]; ring
  have hA : Ar = v * W * u := by
    calc Ar = (v * u) * Ar * (v * u) := by rw [hvu, Matrix.one_mul, Matrix.mul_one]
      _ = v * W * u := by rw [hWdef]; simp only [Matrix.mul_assoc]
  have hu1 : ∀ l j, |u l j| ≤ 1 := by
    intro l j
    rcases lt_trichotomy l j with h | h | h
    · exact (hS.upper l j h).trans (by norm_num)
    · subst h; rw [hS.diag]; simp
    · rw [hS.lower l j h]; simp
  have hWb : ∀ k l, |W k l| ≤ 1 + B := fun k l => by
    nlinarith [hW k l, abs_nonneg (W k l), sq_abs (W k l)]
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hentry : |Ar i j| ≤ (n : ℝ) ^ 2 * |c| * (1 + B) := by
    rw [hA, Matrix.mul_apply]
    calc |∑ l, (v * W) i l * u l j| ≤ ∑ l, |(v * W) i l * u l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin n, (n : ℝ) * (|c| * (1 + B)) := by
        apply Finset.sum_le_sum; intro l _
        rw [abs_mul, Matrix.mul_apply]
        have hin : |∑ k, v i k * W k l| ≤ (n : ℝ) * (|c| * (1 + B)) := by
          calc |∑ k, v i k * W k l| ≤ ∑ k, |v i k * W k l| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ k : Fin n, |c| * (1 + B) := by
              apply Finset.sum_le_sum; intro k _
              rw [abs_mul]
              exact mul_le_mul ((hvc i k).trans (le_abs_self c)) (hWb k l) (abs_nonneg _) hc0
            _ = (n : ℝ) * (|c| * (1 + B)) := by simp
        calc |∑ k, v i k * W k l| * |u l j| ≤ (n : ℝ) * (|c| * (1 + B)) * 1 :=
              mul_le_mul hin (hu1 l j) (abs_nonneg _) (by positivity)
          _ = (n : ℝ) * (|c| * (1 + B)) := by ring
      _ = (n : ℝ) ^ 2 * |c| * (1 + B) := by simp; ring
  have hcast : ((|A i j| : ℤ) : ℝ) = |Ar i j| := by simp [hAr, Int.cast_abs]
  rw [hcast]
  exact hentry

end GlobalTheory.RedTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X], psdCone (bar := bar) (X := X) ⊆ psdCone (bar := (id : ℤ → ℤ)) (X := X) := by
  first | exact @GlobalTheory.PolFan.psdCone_subset_psdCone_int | exact GlobalTheory.PolFan.psdCone_subset_psdCone_int | (intros; apply GlobalTheory.PolFan.psdCone_subset_psdCone_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrank
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.CMTypeCard

theorem card_psi_eq_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  intro E _ _ _ H
  let e : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ GlobalTheory.AllWt.Psi H :=
    { toFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun τ => ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have h1 : Fintype.card (E →+* ℂ) =
      Fintype.card (GlobalTheory.AllWt.Psi H) + Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)).symm
  have h2 : Fintype.card {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} = Fintype.card (GlobalTheory.AllWt.Psi H) :=
    Fintype.card_congr e
  rw [← NumberField.Embeddings.card E ℂ, h1, h2]
  omega

end GlobalTheory.CMTypeCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFramesSpecialiseFlagComponentLocalRing
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CarrySpec

theorem carries_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk :=
  GlobalTheory.CarrySpec.spec_of_anypoint _root_.GlobalTheory.ShFam.CarriesAt.tri_of_carries

end GlobalTheory.CarrySpec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

theorem carrierDim_le_of_add_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  intro O _ bar q ψ lab hlab X _ _ _ _ hX b v hv β₀ hβ₀ hp₀ β hβ hp hin c₀ c hc₀ hc hrel
  obtain ⟨e, he, he'⟩ := hin
  have hw : ∀ k, 0 ≤ c₀ * e k + c k := fun k => add_nonneg (mul_nonneg hc₀.le (he k)) (hc k)
  have hcomb : toReal β = ∑ k, (c₀ * e k + c k) • toReal (v k) := by
    rw [hrel, he', Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, add_smul]
  have hβv : InRCone v β := ⟨_, hw, hcomb⟩
  have hne : ({k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}).Nonempty := ⟨_, b, v, hv, hβv, rfl⟩
  obtain ⟨m, τ, hτ, hβτ, hrank⟩ := Nat.sInf_mem hne
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hτ.strict
  have hψτ : ((ℓ β : ℤ) : ℝ) = N * ψ.evalZ β := by
    obtain ⟨d, hd, hde⟩ := hβτ
    rw [apply_eq_of_toReal_eq hde ℓ]
    have A := (linearOn_iff ψ τ).1 hτ.linear d hd
    rw [← hde, evalR_toReal] at A
    rw [A, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring
  have hψv : ψ.evalZ β = c₀ * ψ.evalZ β₀ + ∑ k, c k * ψ.evalZ (v k) := by
    have A := (linearOn_iff ψ v).1 hv.linear _ hw
    rw [← hcomb, evalR_toReal] at A
    have B := (linearOn_iff ψ v).1 hv.linear e he
    rw [← he', evalR_toReal] at B
    rw [A, B, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hℓv : ((ℓ β : ℤ) : ℝ) = c₀ * ℓ β₀ + ∑ k, c k * ℓ (v k) := by
    rw [apply_eq_of_toReal_eq hcomb ℓ, apply_eq_of_toReal_eq he' ℓ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hk : ∀ k, (N : ℝ) * ψ.evalZ (v k) ≤ ℓ (v k) := fun k => h2 _ (hv.mem k) (hv.nonneg k)
  have h0 : (N : ℝ) * ψ.evalZ β₀ ≤ ℓ β₀ := h2 _ hβ₀ hp₀
  have heq : (N : ℝ) * ψ.evalZ β₀ = ℓ β₀ := by
    have hsum : ∑ k, c k * (N * ψ.evalZ (v k)) ≤ ∑ k, c k * (ℓ (v k) : ℝ) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hc k)
    have E : c₀ * (ℓ β₀ : ℝ) + ∑ k, c k * (ℓ (v k) : ℝ) = c₀ * (N * ψ.evalZ β₀) + ∑ k, c k * (N * ψ.evalZ (v k)) := by
      rw [← hℓv, hψτ, hψv, mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    by_contra hne'
    have hlt : (N : ℝ) * ψ.evalZ β₀ < ℓ β₀ := lt_of_le_of_ne h0 hne'
    have := mul_lt_mul_of_pos_left hlt hc₀
    linarith
  obtain ⟨kk, d, hkk, hd⟩ := h3 β₀ hβ₀ hp₀ heq
  have hβ₀τ : InRCone τ β₀ := by
    refine ⟨fun i => (d i : ℝ) / kk, fun i => by positivity, LinearMap.ext₂ fun a b' => ?_⟩
    have h := LinearMap.congr_fun₂ hd a b'
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h
    have hR : (kk : ℝ) * (β₀ a b' : ℝ) = ∑ i, (d i : ℝ) * (τ i a b' : ℝ) := by exact_mod_cast h
    have hkR : (kk : ℝ) ≠ 0 := by positivity
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    calc (β₀ a b' : ℝ) = ((kk : ℝ) * (β₀ a b' : ℝ)) / kk := by field_simp
      _ = _ := by rw [hR, Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have hle := Nat.sInf_le (s := {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β₀ ∧ genRank γ = k}) ⟨m, τ, hτ, hβ₀τ, rfl⟩
  rw [hlab X hX β hβ hp, hlab X hX β₀ hβ₀ hp₀]
  exact_mod_cast hle.trans hrank.le

end GlobalTheory.PolFan
end
end

