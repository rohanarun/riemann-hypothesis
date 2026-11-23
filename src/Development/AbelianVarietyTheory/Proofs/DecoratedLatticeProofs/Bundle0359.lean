module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumOfVacuaIsVacuumBoth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastVacPf

variable {D : D7}

theorem lastBi_apply {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (u : WO A S) (v : WO S X) :
    lastBi o o'' τ Ξ Φ₂ u v = Φ₂ (o''.resT S v).1 * Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := rfl

theorem heis_left (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (a : WO A S) (v : WO S X) :
    heisO ψ A S a (fun u => lastBi o o'' τ Ξ Φ₂ u v) = fun u =>
      Φ₂ (o''.resT S v).1 * heisO ψ V₀ S ((o.resS S).symm (a, 0)) Ξ ((o.resS S).symm (u, kap τ S (o''.resT S v).2)) := by
  funext u
  simp only [heisO, lastBi_apply]
  have e : (o.resS S).symm (u + a, kap τ S (o''.resT S v).2) =
      (o.resS S).symm (u, kap τ S (o''.resT S v).2) + (o.resS S).symm (a, 0) := by
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
  rw [e, GlobalTheory.LastBiTheta.sOH_resS_symm, GlobalTheory.LastBiTheta.sOH_zero_right, add_zero]
  ring

theorem heis_right (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E)
    (hτ : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram)
    (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ) (b : WO S X) (u : WO A S) :
    heisO ψ S X b (lastBi o o'' τ Ξ Φ₂ u) = o''.boxT S (heisO ψ S T (o''.resT S b).1 Φ₂) (fun w =>
      heisO ψ V₀ S ((o.resS S).symm (0, kap τ S (o''.resT S b).2)) Ξ ((o.resS S).symm (u, kap τ S w))) := by
  obtain ⟨kadd, -, -, -, ksympl, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have kH : ∀ w w', symplOH L S (kap τ S w) (kap τ S w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [ksympl]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_neg]
  show heisO ψ S X b (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm (u, kap τ S w))) = _
  rw [o''.heisO_boxT]
  congr 1
  funext w
  have e : (o.resS S).symm (u, kap τ S (w + (o''.resT S b).2)) =
      (o.resS S).symm (u, kap τ S w) + (o.resS S).symm (0, kap τ S (o''.resT S b).2) := by
    rw [kadd, ← map_add (f := _), Prod.mk_add_mk, add_zero]
  simp only [heisO]
  rw [e, GlobalTheory.LastBiTheta.sOH_resS_symm, GlobalTheory.LastBiTheta.sOH_zero_right, zero_add, kH]

theorem slice_left {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C)
    (v : WO S A') : IsThetaFunO ψ A S fun u => C u v := {
  quasi := fun γ u => h.quasiL γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levL
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 v⟩
  cont := h.cont.comp (continuous_id.prodMk continuous_const)
  smooth := fun n L hL h0 u => by
    have := h.smooth n L 0 hL continuous_const h0 (fun _ => Matrix.map_zero _ (map_zero (finPart D))) u v
    simpa using this }

theorem slice_right {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C)
    (u : WO A S) : IsThetaFunO ψ S A' (C u) := {
  quasi := fun γ v => h.quasiR γ u v
  level := by
    obtain ⟨U, hU, hl⟩ := h.levR
    exact ⟨U, hU, fun a ha h0 => hl a ha h0 u⟩
  cont := h.cont.comp (continuous_const.prodMk continuous_id)
  smooth := fun n L hL h0 v => by
    have := h.smooth n 0 L continuous_const hL (fun _ => Matrix.map_zero _ (map_zero (finPart D))) h0 u v
    simpa using this }

theorem isHalf_mul_left {e : AE D} {k m n : ℕ} (P : Mx D k m) {y : Mx D m n} (h : IsHalf e y) : IsHalf e (P * y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

theorem isHalf_mul_right {e : AE D} {k m n : ℕ} {y : Mx D k m} (P : Mx D m n) (h : IsHalf e y) : IsHalf e (y * P) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem isHalf_add {e : AE D} {m n : ℕ} {y z : Mx D m n} (hy : IsHalf e y) (hz : IsHalf e z) : IsHalf e (y + z) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hy i j, hz i j]

theorem isHalf_zero (e : AE D) (m n : ℕ) : IsHalf e (0 : Mx D m n) := fun i j => by
  rw [Matrix.zero_apply, mul_zero]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {y : Mx D m n} (h : IsHalf e y) : IsHalf e (c • y) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, h i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {y : Mx D m n} (h : IsHalf e y) : IsHalf (cA D e) (adj y) := by
  intro i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [← map_mul, h j i]

theorem isHalf_kap {e : AE D} {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) {w : WO S L''}
    (h : IsHalf e w) : IsHalf (cA D e) (kap τ S w) := by
  unfold kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  exact isHalf_smul _ (isHalf_mul_left _ (isHalf_mul_right _ (isHalf_adj (isHalf_mul_left _ h))))

theorem cA_cA (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    simp only [cA, sigR]
    simp
    congr 1
    exact star_star e

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩
  · rw [cA_cA, mul_comm, h2]
  · rw [cA_cA, add_comm, h3]

theorem isHalf_resS_symm {e : AE D} {V₀ A L : HSp D} (o : OrthDec V₀ A L) (S : HSp D) {a : WO A S} {b : WO L S}
    (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e ((o.resS S).symm (a, b)) := by
  rw [OrthDec.resS_symm_apply]
  exact isHalf_add (isHalf_mul_right _ ha) (isHalf_mul_right _ hb)

theorem isHalf_resT {e : AE D} {X T L'' : HSp D} (o'' : OrthDec X T L'') (S : HSp D) {w : WO S X} (h : IsHalf e w) :
    IsHalf e (o''.resT S w).1 ∧ IsHalf e (o''.resT S w).2 := by
  rw [OrthDec.resT_apply]
  exact ⟨isHalf_mul_left _ h, isHalf_mul_left _ h⟩

theorem smul_latV_mem_latA {S : HSp D} (L : Lat S) (P : Pl D → Prop) {c : D.host.E} (hc : c ∈ D.host.AA)
    {w : Fin S.rank → AE D} (hw : w ∈ latV S L P) : ((1 : AF D.host.F) ⊗ₜ[D.host.F] c : AE D) • w ∈ latA S L P := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hv, a, ha, z, hz, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    refine AddSubgroup.subset_closure ⟨α, hα, hv, c, hc, z, hz, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem latA_orth {S A B : HSp D} (o : OrthDec S A B) (L : Lat S) (LA : Lat A) (LB : Lat B) (x : Pl D)
    (hO : OrthAt o L LA LB x) {z : Fin S.rank → AE D} (hz : z ∈ latA S L (· = x)) :
    o.pA *ᵥ z ∈ latA A LA (· = x) ∧ o.pB *ᵥ z ∈ latA B LB (· = x) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hv, a, ha, z, hz, rfl⟩ := hy
    have h0 : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * z i) : Fin S.rank → AE D) ∈ latV S L (· = x) :=
      AddSubgroup.subset_closure ⟨α, hα, hv, 1, Set.mem_singleton _, z, hz, rfl⟩
    have e : (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * z i) : Fin S.rank → AE D) =
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] a : AE D) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * z i)) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    obtain ⟨hA, hB⟩ := (hO _).1 h0
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact ⟨smul_latV_mem_latA LA _ ha hA, smul_latV_mem_latA LB _ ha hB⟩
  | zero => simp only [Matrix.mulVec_zero]; exact ⟨zero_mem _, zero_mem _⟩
  | add y y' _ _ h h' => simp only [Matrix.mulVec_add]; exact ⟨add_mem h.1 h'.1, add_mem h.2 h'.2⟩
  | neg y _ h => simp only [Matrix.mulVec_neg]; exact ⟨neg_mem h.1, neg_mem h.2⟩

theorem extLat : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (M : Lat V₀) (LA : Lat A) (LL : Lat L) (LS : Lat S)
    (x : Pl D), IsSelfDualC V₀ M → IsSelfDualC A LA → IsSelfDualC L LL → IsSelfDualC S LS → OrthAt o M LA LL x →
    ∀ (a : WO A S) (b : WO L S), a ∈ latO A S (LA : Set _) (LS : Set _) (· = x) → b ∈ latO L S (LL : Set _) (LS : Set _) (· = x) →
      (o.resS S).symm (a, b) ∈ latO V₀ S (M : Set _) (LS : Set _) (· = x) := by
  intro D V₀ A L S o M LA LL LS x hM hLA hLL hLS hO a b ha hb
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D A S LA LS hLA hLS] at ha
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D L S LL LS hLL hLS] at hb
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ S M LS hM hLS, OrthDec.resS_symm_apply]
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    exact add_mem (sum_mem fun k _ => Ideal.mul_mem_right _ _ (ha.1 i k))
      (sum_mem fun k _ => Ideal.mul_mem_right _ _ (hb.1 i k))
  · obtain ⟨hA, hB⟩ := (hO y).1 hy
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact add_mem (ha.2 _ hA) (hb.2 _ hB)

theorem resLat : ∀ (D : D7) (X T L'' S : HSp D) (o'' : OrthDec X T L'') (LX : Lat X) (LT : Lat T) (LZ : Lat L'') (LS : Lat S)
    (x : Pl D), IsSelfDualC X LX → IsSelfDualC T LT → IsSelfDualC L'' LZ → IsSelfDualC S LS → OrthAt o'' LX LT LZ x →
    ∀ w : WO S X, w ∈ latO S X (LS : Set _) (LX : Set _) (· = x) →
      (o''.resT S w).1 ∈ latO S T (LS : Set _) (LT : Set _) (· = x) ∧ (o''.resT S w).2 ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x) := by
  intro D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hO w hw
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S X LS LX hLS hLX] at hw
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hLS hLT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ,
    OrthDec.resT_apply]
  refine ⟨⟨fun i j => ?_, fun y hy => ?_⟩, ⟨fun i j => ?_, fun y hy => ?_⟩⟩
  · show (o''.pA * (w : Matrix (Fin X.rank) (Fin S.rank) (AE D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) i j ∈ _
    rw [Matrix.mul_apply]; exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hw.1 k j)
  · rw [← Matrix.mulVec_mulVec]; exact (latA_orth o'' LX LT LZ x hO (hw.2 y hy)).1
  · show (o''.pB * (w : Matrix (Fin X.rank) (Fin S.rank) (AE D)) : Matrix (Fin L''.rank) (Fin S.rank) (AE D)) i j ∈ _
    rw [Matrix.mul_apply]; exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hw.1 k j)
  · rw [← Matrix.mulVec_mulVec]; exact (latA_orth o'' LX LT LZ x hO (hw.2 y hy)).2

theorem lastVac : ∀ D : D7, GlobalTheory.FinPl.LastVac D := by
  intro D ψ hψ V₀ A L S X T L'' o o'' τ hL hL'' hτ P M LA LS LX LT hM hLA hLS hLX hLT hP Ξ Φ₂ hΞ hΦ
  have hB := GlobalTheory.LastBiTheta.isBiTheta_lastBi D ψ hψ V₀ A L S X T L'' o o'' τ hτ Ξ Φ₂ hΞ.1 hΦ.1
  obtain ⟨kadd, -, -, -, -, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1)
    (by rw [Int.cast_neg, Int.cast_one, neg_one_mul]; exact hτ) (kap τ S) (fun _ => rfl)
  have mono : ∀ {S' T' : HSp D} (LS' : Lat S') (LT' : Lat T') (x : Pl D), P x → ∀ w,
      w ∈ latO S' T' (LS' : Set _) (LT' : Set _) (· = x) → w ∈ latO S' T' (LS' : Set _) (LT' : Set _) P :=
    fun LS' LT' x hx w hw => GlobalTheory.VacLoc.latO_mono _ _ _ _ (fun v hv => hv ▸ hx) hw
  refine ⟨fun v => ⟨slice_left hB v, GlobalTheory.VacLoc.latVac_of_places ψ A S LA LS P _ (slice_left hB v) fun x hx => ?_⟩,
    fun u => ⟨slice_right hB u,
      GlobalTheory.VacLoc.latVac_of_places ψ S X LS LX P _ (slice_right hB u) fun x hx => ?_⟩⟩
  · obtain ⟨-, LL, LZ, hLL, hLZ, hOM, -, -⟩ := hP x hx
    refine ⟨slice_left hB v, fun a ha => ?_, fun e he a ha hh => ?_⟩
    · have hm := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM a 0 ha (zero_mem _))
      have e2 : (o.resS S).symm (2 • a, 0) = 2 • (o.resS S).symm (a, 0) := by
        simp only [two_nsmul]
        rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
      rw [heis_left, e2, hΞ.2.1 _ hm]
      rfl
    · have hm := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM a 0 ha (zero_mem _))
      rw [heis_left, hΞ.2.2 e he _ hm (isHalf_resS_symm o S hh (isHalf_zero e _ _))]
      rfl
  · obtain ⟨-, LL, LZ, hLL, hLZ, hOM, hOX, hk⟩ := hP x hx
    refine ⟨slice_right hB u, fun b hb => ?_, fun e he b hb hh => ?_⟩
    · obtain ⟨h1, h2⟩ := resLat D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hOX b hb
      have hm1 := mono LS LT x hx _ h1
      have hm2 := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM 0 _ (zero_mem _) (hk _ h2))
      have e1 : (o''.resT S (2 • b)).1 = 2 • (o''.resT S b).1 := by
        simp only [two_nsmul, map_add (f := _), Prod.fst_add]
      have e2 : (o.resS S).symm (0, kap τ S (o''.resT S (2 • b)).2) = 2 • (o.resS S).symm (0, kap τ S (o''.resT S b).2) := by
        simp only [two_nsmul]
        rw [map_add (f := _), Prod.snd_add, kadd, ← map_add (f := _), Prod.mk_add_mk, add_zero]
      rw [heis_right ψ o o'' τ hτ, e1, e2, hΦ.2.1 _ hm1, hΞ.2.1 _ hm2]
      rfl
    · obtain ⟨h1, h2⟩ := resLat D X T L'' S o'' LX LT LZ LS x hLX hLT hLZ hLS hOX b hb
      have hm1 := mono LS LT x hx _ h1
      have hm2 := mono M LS x hx _ (extLat D V₀ A L S o M LA LL LS x hM hLA hLL hLS hOM 0 _ (zero_mem _) (hk _ h2))
      obtain ⟨he1, he2⟩ := isHalf_resT o'' S hh
      rw [heis_right ψ o o'' τ hτ, hΦ.2.2 e he _ hm1 he1,
        hΞ.2.2 (cA D e) (isSplitIdem_cA he) _ hm2 (isHalf_resS_symm o S (isHalf_zero _ _ _) (isHalf_kap τ S he2))]
      rfl

end GlobalTheory.LastVacPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatEqOfCarries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BaseCosetPt

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem lat_eq_of_carries {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N₁ N₂ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : Submodule.IsFullLattice E N₁) (h₂ : Submodule.IsFullLattice E N₂)
    (c₁ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₁) (c₂ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₂) :
    N₁ = N₂ := by
  have key : ∀ N : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E N → ∀ x : Fin n → E,
      (x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N) := by
    intro N hN x
    let : Submodule.IsFullLattice E N := hN
    have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) (Submodule.IsFullLattice.span_eq_top (A := E) (M := N))
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  ext x
  rw [key N₁ h₁, key N₂ h₂, c₁, c₂]

end Gen

section Pt

open _root_.Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem frsF_symm_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {w : Sp X.E (R.N j)}
    (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N) : (frsF sel mu p P).symm w ∈ stdAt X.E (R.N j) P.1 := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).1 (by simpa using hw)

theorem frsF_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {x : Sp X.E (R.N j)}
    (hx : x ∈ stdAt X.E (R.N j) P.1) : frsF sel mu p P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).2 hx

theorem cosetIn_eq_of {u : Pr.Word} {j : ℕ} (r : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : Sp X.E (R.N j)) (e : rowSG Pr sel mu → ℤ) (he : e P = 0)
    (hY : r.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) r.1.1.deco.1.N e}) :
    cosetIn r P = {z | z - (frsF sel mu r.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1} := by
  classical
  apply Set.ext
  intro z
  simp only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq, hY]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : y' - y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal r.1.1.deco.1.N := by
      have := (Submodule.mem_iInf _).1 hy' P
      simpa [Submodule.mem_comap, he] using this
    have := add_mem hz (frsF_symm_mem r.1.1 P h1)
    rwa [map_sub, sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, by simp, hz⟩

end Pt

end GlobalTheory.BaseCosetPt

namespace GlobalTheory.BaseCosetPt

open _root_.Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

end GlobalTheory.BaseCosetPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KappaModel
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

theorem kappa_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (s : k) (z₀ : Fin L''.rank → k), s ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * s)) • (fun i => p.pr (ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (FS : Frame k S.rank n) (FL : Frame k L.rank Unit), (∀ r, FL.β r () = s * p.pr (ζ r)) → ∀ TLS, p.IsModel ψ FL FS TLS → ∃ FL'' : Frame k L''.rank Unit, (∀ r, FL''.β r () = z₀ r) ∧ ∃ TL, p.IsModel ψ FS FL'' TL ∧ ∀ (c : SB (Matrix n Unit k)) (Φ : SB (Matrix Unit n k)), (∀ η, Φ.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ())) → ∀ w, TL Φ w = TLS c (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w)) := by
  intro D k _ _ _ _ _ _ p ν hν ψ hψ ψk hk L S L'' ζ τ hrk hτ s z₀ hs hz n _ _ FS FL hFL TLS hTLS
  obtain ⟨-, hk2, hxi, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hk2 ψk hk
  have hz0 : z₀ ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hz
    have h1 := congrFun (congrFun FL.γβ ()) ()
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    have h2 : ∀ r, FL.β r () = 0 := fun r => by
      have h3 := congrFun hz r
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h3
      have hx : p.xi * s ≠ 0 := mul_ne_zero hxi hs
      have h4 : p.pr (ζ r) = 0 := by
        rcases mul_eq_zero.1 h3.symm with h | h
        · exact absurd (neg_eq_zero.1 h) hx
        · exact h
      rw [hFL, h4, mul_zero]
    simp [h2] at h1
  obtain ⟨FL'', hFL''⟩ := exists_frame_col hrk z₀ hz0
  refine ⟨FL'', hFL'', ?_⟩
  set κ : WO S L'' → WO L S := fun w => ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w) with hκdef
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  obtain ⟨hadd, -, -, -, hsy, -⟩ := GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) hτ' κ (fun _ => rfl)
  have hsy' : ∀ w w', symplO L S (κ w) (κ w') = symplO S L'' w w' := fun w w' => by
    rw [hsy]; push_cast; ring
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.KappaModel.finv_hat_neg_one k n ψk ν hcont hne hν
  haveI := hν
  let H : SB (Matrix Unit n k) →ₗ[ℂ] SB (Matrix n Unit k) :=
    { toFun := fun Φ => ⟨finv ψk ν C Φ.1, _root_.GlobalTheory.KappaModel.finv_mem_SB k n ψk ν hcont hne hν C Φ.1 Φ.2⟩
      map_add' := fun Φ Ψ => Subtype.ext (finv_add ψk hcont ν C Φ.2 Ψ.2)
      map_smul' := fun a Φ => Subtype.ext (finv_smul ψk ν C a Φ.1) }
  let TL : SB (Matrix Unit n k) →ₗ[ℂ] (WO S L'' → ℂ) := (LinearMap.funLeft ℂ ℂ κ) ∘ₗ TLS ∘ₗ H
  have hTL : ∀ Φ w, TL Φ w = TLS (H Φ) (κ w) := fun _ _ => rfl
  obtain ⟨-, -, -, hpsi, -⟩ := GlobalTheory.LocSympl.halves_at_split D k p n Unit L S FL FS ψ ψk hk
  have hhalf : ∀ x, IsHalf (cA D p.e) (κ (p.up FS FL'' x)) := fun x =>
    (_root_.GlobalTheory.KappaHalf.ofAdj_rat_mul_half D L S L'' τ p.e _).2 (Witness.up_half p FS FL'' x)
  have hkey : ∀ x a, ψ (symplO L S (p.up FL FS a) (κ (p.up FS FL'' x))) = (ψk (-(∑ r, x () r * a r ())) : ℂ) := by
    intro x a
    rw [hpsi a _ (hhalf x)]
    exact congrArg (fun u => ((ψk u : Circle) : ℂ)) (_root_.GlobalTheory.KappaSplitPairing.key D k p L S L'' ζ τ s z₀ hs hz n FS FL FL'' hFL hFL'' x a)
  refine ⟨TL, ⟨fun Φ => ?_, fun x Φ Φ' h => ?_, fun y hy Φ Φ' h => ?_⟩, fun c Φ hΦ w => ?_⟩
  · exact _root_.GlobalTheory.KappaTheta.isThetaFunO_comp_kappa D ψ L S L'' τ hτ _ (hTLS.theta _)
  · funext w
    show TLS (H Φ') (κ w) = heisO ψ S L'' (p.up FS FL'' x) (fun w => TLS (H Φ) (κ w)) w
    rw [← heis_comp ψ L S L'' κ hadd hsy']
    rw [hTLS.modul (κ (p.up FS FL'' x)) (hhalf x) (H Φ) (H Φ') (fun t => ?_)]
    show finv ψk ν C Φ'.1 t = _ * finv ψk ν C Φ.1 t
    rw [finv_trans ψk ν C x h t, hkey]
  · have hy' : IsHalf p.e (κ y) := (_root_.GlobalTheory.KappaHalf.ofAdj_rat_mul_half D L S L'' τ p.e y).1 hy
    set t₀ := p.down FL FS (κ y) with ht₀
    have hup : p.up FL FS t₀ = κ y := Witness.up_down p FL FS hy'
    have hmod : ∀ t, Φ'.1 t = (ψk (∑ r, t () r * t₀ r ()) : ℂ) * Φ.1 t := fun t => by
      rw [h t, ← hsy', ← hup, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv, hkey, AddChar.map_neg_eq_inv,
        Circle.coe_inv, inv_inv]
    funext w
    show TLS (H Φ') (κ w) = heisO ψ S L'' y (fun w => TLS (H Φ) (κ w)) w
    rw [← heis_comp ψ L S L'' κ hadd hsy', ← hup]
    rw [hTLS.trans t₀ (H Φ) (H Φ') (fun t => finv_mod ψk ν C t₀ hmod t)]
  · show TLS (H Φ) (κ w) = _
    have : H Φ = c := Subtype.ext (hC c.1 c.2 Φ.1 hΦ)
    rw [this]
end GlobalTheory.KappaModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QuotientFiniteLevel

variable {D : D7} {c : Comm D} {v : VCom c} {t : Tup c}

def locK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) : Subgroup (GA D (c.V (j + 1))) :=
  ((F.Q i).T.lev (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega)).J.map
    ((F.Q i).gl (j + 1) ((F.Q i).s - j) (by have := (F.Q i).hs; omega))

def qK (F : QFam v t) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) : Subgroup (GA D (c.V (j + 1))) :=
  ⨆ i, locK F j σ h i

end GlobalTheory.QuotientFiniteLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.FinPl.SplitHalfSuppImp

theorem mxAt_of_isHalf : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) {m n : ℕ} (x : Mx D m n), IsHalf (q.e + cA D q.e) x → MxAt (· = q.v) x := by
  intro D k _ _ _ _ q m n x hx
  exact GlobalTheory.FinPl.SplitHalfSupp.mxAt_of_isHalf_above D k q m n x hx

end GlobalTheory.FinPl.SplitHalfSuppImp

end
end

