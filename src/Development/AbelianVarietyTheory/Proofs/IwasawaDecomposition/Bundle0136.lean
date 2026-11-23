module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Formalism.LocalToGlobal.Columns.LevGCount
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterStepZeroTypePrime
section
noncomputable section

namespace GlobalTheory.Proof.levelCharacter_stepZero_typePrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem supSum_range {κ : Type} [CommRing κ] {n a k : ℕ} (hn : k ≤ n) (ha : k ≤ a) (M : Matrix (Fin n) (Fin n) κ) (f : ℕ → κ)
    (hf : ∀ (i : ℕ) (h : i + 1 < k), f i = M ⟨i, by omega⟩ ⟨i + 1, by omega⟩) :
    supSum a (Finset.range (k - 1)) M = ∑ i ∈ Finset.range (k - 1), f i := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < a ∧ i.val ∈ Finset.range (k - 1) then M i j else 0) =
      if i.val ∈ Finset.range (k - 1) then f i.val else 0 := by
    intro i
    by_cases hi : i.val ∈ Finset.range (k - 1)
    · have hi' := Finset.mem_range.1 hi
      rw [if_pos hi, Finset.sum_eq_single (⟨i.val + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by dsimp only; omega, hi⟩,
        hf _ (by omega)]
      · intro j _ hj
        exact if_neg fun h => hj (Fin.ext h.1.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => if i ∈ Finset.range (k - 1) then f i else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

variable {E : Type} [Field E]

theorem entB_X (q : ℕ) {k n c i : ℕ} (hn : k ≤ n) (hi : i + 1 < k) (ex : ℕ → ℕ) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n ex ex x i (i + 1) = Loc.atN (x (Loc.eN E (n + c) (i + 1))) i := by
  have e1 : LocE.fIdx k c n i = i := if_pos (by omega)
  have e2 : LocE.fIdx k c n (i + 1) = i + 1 := if_pos hi
  have e3 : LocE.scE n ex i = 0 := if_pos (by omega)
  have e4 : LocE.scE n ex (i + 1) = 0 := if_pos (by omega)
  unfold LocE.entB
  rw [e1, e2, e3, e4]
  simp

theorem symLevelFrameEntry_superdiag_second_block (q : ℕ) {k n c i : ℕ} (hi : i + 1 < c) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n (fun i => i + 1) (fun i => i + 1) x (k + i) (k + i + 1) =
      (q : E) * Loc.atN (x (Loc.eN E (n + c) (n + i + 1))) (n + i) := by
  have e1 : LocE.fIdx k c n (k + i) = n + i := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e2 : LocE.fIdx k c n (k + i + 1) = n + i + 1 := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e3 : LocE.scE n (fun i => i + 1) (n + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
    unfold LocE.scE
    rw [if_neg (by omega), if_neg (by omega)]
    beta_reduce
    omega
  unfold LocE.entB
  rw [e1, e2, e3, zpow_one, mul_comm]

theorem chrG_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true)
    (hψ : ∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) :
    ChrG Ch sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  have hm := R.two_le_m
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hc : R.r - R.k - 1 = cOf R 0 - 1 := by unfold Ranks.r cOf; omega
  have hl : colLev Ch 0 ⟨P.1, hP⟩ = ⟨HX (𝓞 X.E ⧸ P.1.asIdeal) (R.N 0) R.k R.t 0,
      lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0⟩ := if_pos (by omega)
  rw [hl]
  intro hbar g r hr hrg hg
  have hq : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hp0 : psi0P Ch P.1 = Ch.psi0 ⟨P.1, hP⟩ := dif_pos hP
  have hJ := hr.2
  simp only [Jat, hP, hs, if_true] at hJ
  have hst : r ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N 0) (cOf R 0) fun i => i + 1) := by
    have h1 := hJ.1
    simpa using h1
  have hint := fun p p' => GlobalTheory.LastSteps.entB_int (P := P.1) R.k (x := r.toLinearMap) (fun y hy => (hst y).2 hy) p p'
  have ha := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r hst
  have h2 : ∑ i ∈ Finset.range (R.r - R.k - 1), LocE.entB (qOf P.1) R.k (cOf R 0) (R.N 0) (cOf R 0) (R.N 0)
      (fun i => i + 1) (fun i => i + 1) r.toLinearMap (R.k + i) (R.k + i + 1) = (qOf P.1 : X.E) * Loc.n1Arg r := by
    rw [hc, Loc.n1Arg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    exact symLevelFrameEntry_superdiag_second_block _ (by omega) _
  have h3 : cst.psi P (Loc.n1Arg r) = psi0P Ch P.1 (redP P.1 ((qOf P.1 : X.E) * Loc.n1Arg r)) := by
    rw [← hψ _ ha, mul_div_cancel_left₀ _ hq]
  have h4 : ((lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0 hbar : X.Kˣ) : X.K) =
      Ch.psi0 ⟨P.1, hP⟩ (supSum R.k (Finset.range (R.k - 1)) hbar.1.1) := by
    show ((lamGen _ _ _ R.k [] (SX R.k R.m 0) hbar : X.Kˣ) : X.K) = _
    rw [lamGen_nil, SX_zero]
    rfl
  refine h4.trans ?_
  simp only [chiInv, lamRow, hP, hs, if_true, LocE.lamGBS, LocE.lamGvS, inv_one, one_mul, mul_one, Finset.range_zero,
    Finset.prod_empty]
  rw [h2, h3, hp0, reduction_add (GlobalTheory.TopStep.intAt_sum _ fun i _ => hint _ _) ha, AddChar.map_add_eq_mul,
    GlobalTheory.TopStep.reduction_sum₂ _ fun i _ => hint _ _, mul_comm, mul_inv_cancel_right₀ (AddChar.val_isUnit _ _).ne_zero]
  congr 1
  refine supSum_range hN.ge le_rfl _ _ fun i hi => ?_
  have hi1 : i + 1 < R.N 0 := by omega
  have hi0 : i < R.N 0 := by omega
  have he : Loc.eN X.E (R.N 0 + cOf R 0) (i + 1) = Loc.inX X.E (R.N 0) (cOf R 0) (Loc.eN X.E (R.N 0) (i + 1)) := by
    funext l
    rw [GlobalTheory.QNormal.inX_apply]
    unfold Loc.eN
    split_ifs <;> first | rfl | omega
  have hv : redV P.1 (Loc.eN X.E (R.N 0) (i + 1)) = Pi.single ⟨i + 1, hi1⟩ 1 := by
    funext l
    simp only [redV, Loc.eN, Pi.single_apply, Fin.ext_iff]
    split_ifs
    · exact GlobalTheory.TopStep.reduction_one₂
    · exact GlobalTheory.TopStep.reduction_zero
  have h5 := congrFun (hg _ (GlobalTheory.GO.ChRoot.eN_mem (i := i + 1))) ⟨i, hi0⟩
  rw [hv, Matrix.mulVec_single_one] at h5
  rw [entB_X _ hN.ge hi, he, LinearEquiv.coe_coe, hrg, Loc.atN, dif_pos (by omega), GlobalTheory.QNormal.inX_apply, dif_pos hi0]
  exact h5

end GlobalTheory.Proof.levelCharacter_stepZero_typePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionStepZeroTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.ZeroGrp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

def autOf (A : GL (Fin n) (𝓞 E)) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinear (Matrix.toLin' (A.1.map (algebraMap (𝓞 E) E))) (Matrix.toLin' ((A⁻¹).1.map (algebraMap (𝓞 E) E)))
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one])

omit [StarRing E] in
theorem autOf_apply (A : GL (Fin n) (𝓞 E)) (x : Sp E n) (i : Fin n) :
    autOf A x i = ∑ j, algebraMap (𝓞 E) E (A.1 i j) * x j := rfl

omit [StarRing E] in
theorem autOf_inv (A : GL (Fin n) (𝓞 E)) : (autOf A)⁻¹ = autOf A⁻¹ := LinearEquiv.ext fun _ => rfl

omit [StarRing E] in
theorem extE_lt (c : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) (l : Fin (n + c)) :
    CongLevel.extE c g v l = if h : l.1 < n then g (CongLevel.resX c v) ⟨l.1, h⟩ else v l := by
  rw [CongLevel.extE_apply, Pi.add_apply, CongLevel.inX_apply]
  split_ifs with h
  · have : CongLevel.resX c v ⟨l.1, h⟩ = v l := rfl
    rw [Pi.sub_apply, this]
    ring
  · rw [add_zero]

theorem extE_maps_scl {q c : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (he : ∀ i j, i ≤ j → j < n → e i ≤ e j)
    (A : GL (Fin n) (𝓞 E)) (hA : ∀ i j : Fin n, j.1 < i.1 → A.1 i j = 0) (v : Sp E (n + c))
    (hv : v ∈ LocE.sclLat P q (n + c) e) : CongLevel.extE c (autOf A) v ∈ LocE.sclLat P q (n + c) e := by
  rw [CongLevel.mem_sclLat] at hv ⊢
  intro l
  rw [extE_lt]
  split_ifs with h
  · rw [autOf_apply, Finset.mul_sum]
    refine TopStep.intAt_sum _ fun j _ => ?_
    by_cases hj : j.1 < l.1
    · rw [hA ⟨l.1, h⟩ j hj]
      simpa using TopStep.intAt_zero
    · obtain ⟨d, hd⟩ := Int.le.dest (he l.1 j.1 (by omega) j.2)
      have h1 := ((IntAt.coe P (A.1 ⟨l.1, h⟩ j)).mul (TopStep.intAt_pow (TopStep.intAt_nat q) d)).mul
        (hv (Fin.castAdd c j))
      convert h1 using 1
      have : CongLevel.resX c v j = v (Fin.castAdd c j) := rfl
      rw [this, Fin.val_castAdd, ← hd, zpow_add₀ hq, zpow_natCast]
      have := zpow_ne_zero (e l.1) hq
      field_simp
  · exact hv l

theorem uni_iff {κ : Type} [CommRing κ] {a : ℕ} (ha : n = a) {M : GL (Fin n) κ} :
    M ∈ uniUT n κ a [] ↔ (∀ i j : Fin n, j.1 < i.1 → M.1 i j = 0) ∧ ∀ i, M.1 i i = 1 := by
  subst ha
  rw [mem_uniUT]
  refine ⟨fun h => ⟨fun i j => h.2.1 i j i.2, fun i => h.2.2 i i.2⟩, fun h => ⟨fun i j hij => ?_, fun i j _ => h.1 i j,
    fun i _ => h.2 i⟩⟩
  have : coarse n [] j.1 < coarse n [] i.1 := hij
  rw [coarse_of_lt i.2] at this
  omega

theorem extE_stab_scl {q c : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (he : ∀ i j, i ≤ j → j < n → e i ≤ e j)
    (A : GL (Fin n) (𝓞 E)) (hA : A ∈ uniUT n (𝓞 E) n []) :
    CongLevel.extE c (autOf A) ∈ stabL E (n + c) (LocE.sclLat P q (n + c) e) := by
  intro v
  refine ⟨fun hv => ?_, extE_maps_scl hq e he A ((uni_iff rfl).1 hA).1 v⟩
  have h := extE_maps_scl hq e he A⁻¹ ((uni_iff rfl).1 (inv_mem hA)).1 _ hv
  rw [← autOf_inv, ← CongLevel.extE_inv] at h
  rwa [show (CongLevel.extE c (autOf A))⁻¹ (CongLevel.extE c (autOf A) v) = v from LinearEquiv.symm_apply_apply _ v] at h

omit [NumberField E] [StarRing E] in
theorem bvecS_eq (q rS c : ℕ) (f : Fin n) :
    LocE.bvecS E q n rS n c (f.1 + rS) = Loc.inX E n c (Pi.single f 1) := by
  have h1 : LocE.fIdx n c n (symIdxInv n rS (f.1 + rS)) = f.1 := by
    have := f.2
    unfold LocE.fIdx symIdxInv
    split_ifs <;> omega
  unfold LocE.bvecS LocE.bvecG
  rw [h1]
  unfold LocE.scE
  rw [if_pos f.2, zpow_zero, one_smul]
  funext l
  rw [CongLevel.inX_apply]
  unfold Loc.eN
  have := f.2
  by_cases h : l.1 < n
  · rw [dite_eq_left h, Pi.single_apply]
    simp [Fin.ext_iff]
  · rw [dite_eq_right h, if_neg (by omega)]

theorem inX_mem_flagS (q rS c : ℕ) (f : Fin n) (x : Sp E n) :
    Loc.inX E n c x ∈ LocE.flagS P q n rS n c (f.1 + rS) ↔
      ∀ l : Fin n, IntAt P (((q : E) ^ (if f.1 ≤ l.1 then (1 : ℤ) else 0))⁻¹ * x l) := by
  unfold LocE.flagS
  rw [CongLevel.mem_sclLat]
  have key : ∀ l, l < n → (LocE.scE n (fun i => i + 1) l +
      if LocE.bd5 n rS (f.1 + rS) ≤ symIdx n rS (LocE.fPos n c n l) then (1 : ℤ) else 0) = if f.1 ≤ l then 1 else 0 := by
    intro l hl
    have := f.2
    unfold LocE.scE LocE.bd5 LocE.fPos symIdx
    rw [if_pos hl, if_pos hl, if_pos hl, if_neg (by omega : ¬ f.1 + rS = rS + n), zero_add]
    simp
  constructor
  · intro h l
    have h1 := h (Fin.castAdd c l)
    rw [key _ (by simp), CongLevel.inX_apply, dite_eq_left (by simp)] at h1
    exact h1
  · intro h l
    rw [CongLevel.inX_apply]
    by_cases hl : l.1 < n
    · rw [dite_eq_left hl, key _ hl]
      exact h ⟨l.1, hl⟩
    · rw [dite_eq_right hl, mul_zero]
      exact TopStep.intAt_zero

theorem extE_mem_JGsym {q : ℕ} (hq : (q : E) ≠ 0) (rS r t c : ℕ) (A : GL (Fin n) (𝓞 E)) (hA : A ∈ uniUT n (𝓞 E) n []) :
    CongLevel.extE c (autOf A) ∈ LocE.JGsym P q n rS r t n c := by
  have hs : ∀ s, CongLevel.extE c (autOf A) ∈ stabL E (n + c) (LocE.flagS P q n rS n c s) := by
    intro s
    refine extE_stab_scl hq _ (fun i j hij hj => ?_) A hA
    have hi : i < n := by omega
    unfold LocE.scE LocE.fPos symIdx
    simp only [if_pos hi, if_pos hj]
    split_ifs <;> omega
  refine ⟨extE_stab_scl hq _ (fun i j hij hj => ?_) A hA, fun s _ => hs s, fun s _ => ⟨hs s, ?_⟩⟩
  · unfold LocE.scE
    rw [if_pos hj, if_pos (by omega)]
  · by_cases h : rS ≤ s ∧ s < rS + n
    · obtain ⟨f, rfl⟩ : ∃ f : Fin n, s = f.1 + rS := ⟨⟨s - rS, by omega⟩, by simp only; omega⟩
      rw [bvecS_eq, CongLevel.extE_inX, ← map_sub, inX_mem_flagS]
      intro l
      obtain ⟨h1, h2⟩ := (uni_iff rfl).1 hA
      have e : (autOf A (Pi.single f 1) - (Pi.single f 1 : Sp E n)) l =
          algebraMap (𝓞 E) E (A.1 l f) - (Pi.single f 1 : Sp E n) l := by
        rw [Pi.sub_apply, autOf_apply]
        simp [Pi.single_apply]
      rw [e]
      split_ifs with hl
      · by_cases hlf : l = f
        · subst hlf
          simpa [h2] using TopStep.intAt_zero
        · have : f.1 < l.1 := lt_of_le_of_ne hl fun h => hlf (Fin.ext h.symm)
          simpa [h1 l f this, hlf] using TopStep.intAt_zero
      · have hlf : l ≠ f := fun h => hl (h ▸ le_rfl)
        simpa [hlf] using IntAt.coe P (A.1 l f)
    · obtain ⟨i, hi⟩ : ∃ i, LocE.fIdx n c n (symIdxInv n rS s) = n + i :=
        ⟨LocE.fIdx n c n (symIdxInv n rS s) - n, by unfold LocE.fIdx symIdxInv; split_ifs <;> omega⟩
      unfold LocE.bvecS LocE.bvecG
      rw [hi, map_smul, CongLevel.extE_apply, CongLevel.resX_eN]
      simp

omit [StarRing E] in
theorem exists_lift (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) (hM : M ∈ uniUT n _ n []) :
    ∃ A ∈ uniUT n (𝓞 E) n [], ∀ i j, Ideal.Quotient.mk P.asIdeal (A.1 i j) = M.1 i j := by
  obtain ⟨h1, h2⟩ := (uni_iff rfl).1 hM
  choose a ha using fun i j => Ideal.Quotient.mk_surjective (M.1 i j)
  let B : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => if j.1 < i.1 then 0 else if i = j then 1 else a i j
  have hB : B.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := B) (fun i j hij => if_pos (show j.1 < i.1 from hij))]
    simp [B]
  refine ⟨Matrix.GeneralLinearGroup.mk'' B (by rw [hB]; exact isUnit_one), (uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩,
    fun i j => ?_⟩
  · exact if_pos hij
  · show B i i = 1
    simp [B]
  · show Ideal.Quotient.mk P.asIdeal (if j.1 < i.1 then 0 else if i = j then 1 else a i j) = _
    split_ifs with c1 c2
    · rw [h1 i j c1, map_zero]
    · rw [c2, h2, map_one]
    · exact ha i j

theorem uni_iff_prX {k : ℕ} (hn : n = k) (rS r t c : ℕ) (hr : k + rS ≤ r) (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) :
    M ∈ uniUT n _ k [] ↔ ∃ g ∈ Loc.prX (Loc.Cbe (LocE.JGsym P (qOf P) k rS r t n c) 1),
      ∀ x ∈ stdAt E n P, redV P (g x) = M.1.mulVec (redV P x) := by
  subst hn
  have hq := TopStep.qOf_ne_zero (P := P)
  have hc : ∀ ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c), ρ ∈ Loc.Cbe (LocE.JGsym P (qOf P) n rS r t n c) 1 ↔
      ρ ∈ Loc.R1 E n c ∧ ρ ∈ LocE.JGsym P (qOf P) n rS r t n c := by
    intro ρ
    simp [Loc.Cbe]
  constructor
  · intro hM
    obtain ⟨A, hA, hAM⟩ := exists_lift M hM
    refine ⟨autOf A, ⟨CongLevel.extE c (autOf A), (hc _).2 ⟨CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ _, extE_mem_JGsym hq _ _ _ _ A hA⟩,
      CongLevel.extE_inX _ _⟩, fun x hx => ?_⟩
    funext i
    have hx' := TopStep.mem_stdAt.1 hx
    show redP P (autOf A x i) = ∑ j, M.1 i j * redP P (x j)
    rw [autOf_apply, TopStep.reduction_sum₂ _ fun j _ => (IntAt.coe P _).mul (hx' j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [reduction_mul (IntAt.coe P _) (hx' j), reduction_coe, hAM]
  · rintro ⟨g, ⟨ρ, hρ, hg⟩, hM⟩
    have key : ∀ f l : Fin n, f.1 ≤ l.1 → M.1 l f = (Pi.single f 1 : Fin n → 𝓞 E ⧸ P.asIdeal) l := by
      intro f l hl
      have h1 := (((hc ρ).1 hρ).2.2.2 (f.1 + rS) (by have := f.2; omega)).2
      rw [bvecS_eq, hg, ← map_sub, inX_mem_flagS] at h1
      have h2 := h1 l
      rw [if_pos hl, zpow_one, mul_comm, ← div_eq_mul_inv, Pi.sub_apply] at h2
      have h3 := TopStep.redP_eq_zero_of_div h2
      have h4 : IntAt P (g (Pi.single f 1) l - (Pi.single f 1 : Sp E n) l) := by
        have := (TopStep.intAt_nat (qOf P)).mul h2
        rwa [mul_div_cancel₀ _ hq] at this
      have h5 := reduction_add h4 (TopStep.mem_stdAt.1 (TopStep.single_mem_stdAt (P := P) f) l)
      rw [sub_add_cancel, h3, zero_add] at h5
      have h6 := congrFun (hM _ (TopStep.single_mem_stdAt f)) l
      rw [TopStep.redV_single, Matrix.mulVec_single_one] at h6
      rw [← TopStep.redV_single]
      exact h6.symm.trans h5
    refine (uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [key j i hij.le, Pi.single_eq_of_ne fun h => by rw [h] at hij; omega]
    · rw [key i i le_rfl, Pi.single_eq_same]

theorem grpG_zero : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → GrpG sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  intro X Pr R Ch sel S mu cst P hP hs _ M
  have hm := R.two_le_m
  have e1 : (colLev Ch 0 ⟨P.1, hP⟩).H = uniUT (R.N 0) _ R.k [] := by
    unfold colLev
    rw [if_pos (by omega)]
    rfl
  have e2 : Jat (Pr := Pr) cst.sharp 0 P.1 = LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N 0) (cOf R 0) := by
    unfold Jat
    rw [if_pos hP, if_pos hs]
  unfold prCat
  rw [e1, e2]
  exact uni_iff_prX (by simp [Ranks.N]) _ _ _ _ (by unfold Ranks.rS Ranks.r; omega) M

end GlobalTheory.Mem.ZeroGrp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexForm
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbNormTie

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_eq_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem j_eq_sum {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, LinearMap.map_smulₛₗ]

theorem j_ne_zero {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    {x : Fin n → K} (hx : x ≠ 0) : j x ≠ 0 := by
  intro h0
  apply hx
  funext i
  rw [j_eq_sum] at h0
  have := Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i
  simpa using this

theorem normAt_sq {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (Xf : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b Xf v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b Xf v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem hAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H : Matrix (Fin n) (Fin n) K)
    (hin : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y)) :
    (∀ x y, hAt H (InfinitePlace.mk σ) x y = inner ℂ (j x) (j y)) ∨
      (∀ x y, hAt H (InfinitePlace.mk σ) x y = star (inner ℂ (j x) (j y))) := by
  rcases InfinitePlace.embedding_mk_eq σ with he | he
  · left
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hσ]
    rfl
  · right
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]

theorem posAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K)
    (op : W →ₗ[ℂ] W) (hT : FormsTie σ j H E op) :
    PosAt H (InfinitePlace.mk σ) ∧ ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; simp [Complex.star_def]
  refine ⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩
  · rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, h]; exact (inner_conj_symm (j y) (j x)).symm
    · rw [h, h, star_star]; exact inner_conj_symm (j x) (j y)
  · rw [hd, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2

end GlobalTheory.AmbNormTie


open GlobalTheory.AmbNormTie in
theorem GlobalTheory.AmbNormTie.normAt_frm_mk : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  intro K _ _ _ _ σ hσ W _ _ n j H E op hT x
  obtain ⟨hP, hd⟩ := posAt_mk hσ j H E op hT
  have hPD := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x =
      hAt H (InfinitePlace.mk σ) x x := by
    rw [Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2,
      GlobalTheory.Core.AmbTieStep.hAt_eq_dot]
  have h2 := normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x
  rw [hmaj, hd, Complex.ofReal_re] at h2
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2
end

