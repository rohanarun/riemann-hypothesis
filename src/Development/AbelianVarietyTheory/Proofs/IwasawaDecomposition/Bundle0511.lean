module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangular
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q : ℕ}

theorem blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    (b : Matrix (Fin q) (Fin q) ℂ) :
    (fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b =
      fromBlocks (aᴴ * S.toBlocks₁₁ * a) (aᴴ * S.toBlocks₁₂ * b) (bᴴ * S.toBlocks₂₁ * a) (bᴴ * S.toBlocks₂₂ * b) := by
  conv_lhs => rw [← fromBlocks_toBlocks S]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply]

theorem schur_blockDiag_conj (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (a : Matrix (Fin p) (Fin p) ℂ)
    {b : Matrix (Fin q) (Fin q) ℂ} (hb : IsUnit b.det) :
    schur ((fromBlocks a 0 0 b)ᴴ * S * fromBlocks a 0 0 b) = aᴴ * schur S * a := by
  have hb' : IsUnit bᴴ.det := by rw [det_conjTranspose]; exact hb.star
  rw [blockDiag_conj, schur, schur]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  rw [mul_nonsing_inv_cancel_left _ _ hb, nonsing_inv_mul_cancel_left _ _ hb']

theorem reindex_conj_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (A : Matrix (Fin r) (Fin r) ℂ)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (fromBlocks (uni w.2.2) 0 0 (uni w.2.1))ᴴ * shear (reindex e e A) (toMat w.1) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
  have h1 : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  have h2 : fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) =
      (fromBlocks 1 (toMat w.1) 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
        fromBlocks (uni w.2.2) 0 0 (uni w.2.1) := by
    simp [fromBlocks_multiply]
  rw [h1, reindex_uni_glue he, h2, shear]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem dens_glue : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  intro r p q e he A w hS
  have hR := reindex_conj_glue he A w
  set S := shear (reindex e e A) (toMat w.1) with hSdef
  set H := (uni (glue e w))ᴴ * A * uni (glue e w) with hH
  have h22 : (reindex e e H).toBlocks₂₂ = (uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1 := by
    rw [hR, blockDiag_conj, toBlocks_fromBlocks₂₂]
  have hd : (reindex e e H).toBlocks₂₂.det = S.toBlocks₂₂.det := by
    rw [h22, det_mul, det_mul, det_conjTranspose, det_uni]; simp
  have hs : schur (reindex e e H) = (uni w.2.2)ᴴ * schur S * uni w.2.2 := by
    rw [hR, schur_blockDiag_conj _ _ (by rw [det_uni]; exact isUnit_one)]
  obtain ⟨m1, m2⟩ := _root_.GlobalTheory.FlagFibre.lminor_block r p q e he H (hd ▸ hS)
  rw [hd, hs] at m2
  rw [h22] at m1
  unfold dens
  rw [← hH, ← Equiv.prod_comp e.symm, Fintype.prod_sum_type]
  have a1 : ∀ a : Fin q, lminor H (e.symm (Sum.inr a)).castSucc =
      lminor ((uni w.2.1)ᴴ * S.toBlocks₂₂ * uni w.2.1) a.castSucc := fun a => m1 _ _ (by simp [he.2])
  have a2 : ∀ a : Fin p, lminor H (e.symm (Sum.inl a)).castSucc =
      S.toBlocks₂₂.det * lminor ((uni w.2.2)ᴴ * schur S * uni w.2.2) a.castSucc := fun a => m2 _ _ (by simp [he.1])
  simp only [a1, a2, norm_mul, mul_zpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← zpow_natCast, ← _root_.zpow_mul, neg_mul]
  ring

end GlobalTheory.FlagFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomain
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_pos_of_posDef {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) (k : Fin (m + 1)) :
    0 < lminor M k :=
  (h.submatrix (Fin.castLE_injective _)).det_pos

theorem lminor_neg' {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (k : Fin (m + 1)) :
    lminor (-M) k = (-1) ^ (k : ℕ) * lminor M k := by
  unfold lminor
  rw [submatrix_neg, Pi.neg_apply, Pi.neg_apply, det_neg, Fintype.card_fin]

theorem psgn_of_le' {q i : ℕ} (h : i ≤ q) : psgn q i = 1 :=
  Finset.prod_eq_one fun a ha => by
    have := Finset.mem_range.1 ha
    simp [sgn, show a < q by omega]

theorem psgn_add' (q k : ℕ) : psgn q (q + k) = (-1) ^ k := by
  induction k with
  | zero => simpa using psgn_of_le' (le_refl q)
  | succ k ih =>
    have : psgn q (q + (k + 1)) = psgn q (q + k) * sgn q (q + k) := Finset.prod_range_succ _ _
    rw [this, ih]
    simp [sgn, pow_succ]

theorem signs_of_blocks {r p q : ℕ} {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (H : Matrix (Fin r) (Fin r) ℂ)
    (h2 : (reindex e e H).toBlocks₂₂.PosDef) (hs : (-schur (reindex e e H)).PosDef) (i : Fin (r + 1)) :
    0 < psgn q i * (lminor H i).re := by
  obtain ⟨h₁, h₂⟩ := GlobalTheory.FlagFibre.lminor_block r p q e he H h2.det_pos.ne'.isUnit
  have hr := he.card
  by_cases hi : (i : ℕ) ≤ q
  · rw [psgn_of_le' hi, one_mul, h₁ i ⟨i, by omega⟩ rfl]
    exact (Complex.pos_iff.1 (lminor_pos_of_posDef h2 _)).1
  · have hi2 := i.2
    obtain ⟨k, hk⟩ : ∃ k : Fin (p + 1), (i : ℕ) = q + k := ⟨⟨i - q, by omega⟩, by simp only; omega⟩
    have h3 := mul_pos h2.det_pos (lminor_pos_of_posDef hs k)
    rw [lminor_neg'] at h3
    rw [h₂ i k hk, hk, psgn_add', ← Complex.re_ofReal_mul]
    have h4 := (Complex.pos_iff.1 h3).1
    convert h4 using 2
    push_cast
    ring

theorem signs_over_dom : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ),
    reindex e e A = -Jpq p q → ∀ y : Low r → ℂ, toMat (base e y) ∈ hcDom p q →
    ∀ i : Fin (r + 1), 0 < psgn q i * (lminor ((uni y)ᴴ * A * uni y) i).re := by
  intro r p q e he A hA y hy i
  obtain ⟨w, rfl⟩ := glue_surjective he y
  rw [base_glue he] at hy
  have hy' : (1 - (toMat w.1)ᴴ * toMat w.1).PosDef := hy
  have hinj : ∀ {m : ℕ} (u : Low m → ℂ), Function.Injective (uni u).mulVec := fun u =>
    mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (by rw [det_uni]; exact isUnit_one))
  set Z := toMat w.1 with hZ
  set a := uni w.2.2 with ha
  set b := uni w.2.1 with hb
  have hH : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
      fromBlocks (-(aᴴ * a)) (-(aᴴ * Z * b)) (-(aᴴ * Z * b))ᴴ (bᴴ * (1 - Zᴴ * Z) * b) := by
    have : reindex e e ((uni (glue e w))ᴴ * A * uni (glue e w)) =
        (reindex e e (uni (glue e w)))ᴴ * reindex e e A * reindex e e (uni (glue e w)) := by
      simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [this, reindex_uni_glue he, hA, Jpq, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply]
    congr 1
    · simp [ha]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [ha, hb, hZ, Matrix.mul_assoc]
    · simp [hb, hZ, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_neg_add]
  have h2 : (bᴴ * (1 - Zᴴ * Z) * b).PosDef := hy'.conjTranspose_mul_mul_same (hinj _)
  refine signs_of_blocks he _ ?_ ?_ i
  · rw [hH, toBlocks_fromBlocks₂₂]; exact h2
  · rw [hH, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
      neg_sub, sub_neg_eq_add, add_comm]
    refine PosDef.add_posSemidef ?_ (h2.inv.posSemidef.mul_mul_conjTranspose_same _)
    simpa using (PosDef.one (n := Fin p) (R := ℂ)).conjTranspose_mul_mul_same (hinj w.2.2)

end GlobalTheory.FlagFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.Proof.LetterConjugation

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem mem_letters (x : Letter Dw) : x ∈ letters Dw := by
  obtain ⟨τ, i⟩ := x
  obtain ⟨a, rfl⟩ := (Fintype.equivFin (E →+* ℂ)).symm.surjective τ
  exact List.mem_flatMap.2 ⟨a, List.mem_finRange a, List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩⟩

theorem nodup_letters : (letters Dw).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · exact (List.nodup_finRange _).map fun i i' h => eq_of_heq (Sigma.mk.inj h).2
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, h⟩ := List.mem_map.1 hy
    exact hab ((Fintype.equivFin (E →+* ℂ)).symm.injective (Sigma.mk.inj h).1).symm

theorem rt0_conj_neg_ne_zero : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h2
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h2
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, him] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem conj_ne {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h1
  exact rt0_conj_neg_ne_zero (H := H) (by simpa [conjEmb, h] using h1)

theorem conj_eq {τ : E →+* ℂ} (h : τ (H.rt : E) ≠ H.rt0) : conjEmb τ (H.rt : E) = H.rt0 := by
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h0, H.sqrt_neg_disc_sq]; simp
  have h2 : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h1).resolve_left h
  have h3 : starRingEnd ℂ H.rt0 ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, H.sqrt_neg_disc_sq]; simp
  have h4 : starRingEnd ℂ H.rt0 = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 h3).resolve_left rt0_conj_neg_ne_zero
  simp [conjEmb, h2, h4]

theorem mult_add (τ : E →+* ℂ) : Dw.mult τ + Dw.mult (conjEmb τ) = Dw.p + Dw.q := by
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (conj_ne h)]
  · rw [if_neg h, if_pos (conj_eq h), add_comm]

theorem two_mul_length : 2 * (letters Dw).length = Module.finrank ℚ E * (Dw.p + Dw.q) := by
  classical
  have h1 : (letters Dw).length = ∑ τ, Dw.mult τ := by
    rw [← List.toFinset_card_of_nodup (nodup_letters Dw),
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_letters Dw x), Finset.card_univ, Fintype.card_sigma]
    simp
  have hinv : Function.Involutive (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := fun τ => by
    ext x; simp [conjEmb]
  have h2 : ∑ τ, Dw.mult (conjEmb τ) = ∑ τ, Dw.mult τ := hinv.bijective.sum_comp Dw.mult
  rw [h1, two_mul]
  nth_rewrite 2 [← h2]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => mult_add Dw τ, Finset.sum_const, Finset.card_univ,
    Embeddings.card, smul_eq_mul]

end Free

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

end GlobalTheory.Proof.LetterConjugation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevIsReadsTw
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel

namespace GlobalTheory.SeeSaw.TwLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cl_nonempty {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) : Nonempty (I.stX a).Cl := by
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  exact ⟨⟨(), Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩⟩

theorem q_inj {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ P P' : I.Q a, underPl B.host.F P.1 = underPl B.host.F P'.1 → P = P' := by
  classical
  intro P P' e
  rcases (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).1 (HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal e.symm)) with h | h
  · exact Subtype.ext h.symm
  · exact absurd (h ▸ Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P'.2))
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).1.split P.1 (Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P.2)))


set_option maxHeartbeats 2000000 in
theorem levIs_reads_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (a : I.ι) (ha : a ≠ I.mu0) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}
    (hO : letI := Formalism.BasicNotions.tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F);
      ∀ᶠ (u : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) in nhds 1,
        ∀ κ : S.U, κ.1 = u → S.chi κ = 1)
    (hK : I.ReadsP a S.Lb S.U S.chi y lat st)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.LLˣ) : B.LL))
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ c (w : (B.primes X).vGs) x, ((cg (c + 1) w.1 x : ℂˣ) : ℂ) = B.embLL ((Formalism.L2.Col.chiAt I.Ch w c x : B.LLˣ) : B.LL))
    (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hξ : ∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL))
    (hr : B.R.r ≤ (I.rec7 l Z).sp.X'.rank),
    LevIs S (levS _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B))
      (Lev.levChi _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B)) := by
  intro B X I hOk hPins l Z a ha bad S y lat st hO hK P' hH hchi cg hcg ξ hξ hr
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hLb : S.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  obtain ⟨c⟩ := cl_nonempty I a
  have hR := GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary (Q := I.Q a) B.sp.cm gP S (rowTyG I.Ch I.Ps) B.embLL _ _ (GlobalTheory.Mem.Col2.ChEx.q_conj I hOk a)
    (q_inj I hOk a) hO (GlobalTheory.T.twistedTuple_reading_level_character I hOk hPins l Z a S hK c ξ hξ)
  have key := @_root_.GlobalTheory.SeeSaw.TwLev.lev_iffQ B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ S hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs (I.Q a) I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL ξ hR
    P' cg hH hchi hcg
  show (∀ h, h ∈ levS _ 1 _ ↔ _) ∧ _
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => (key _ κ.1 hκ.2).2 κ.2⟩
  obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
  exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩

end GlobalTheory.SeeSaw.TwLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.CoordComp

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)


open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem comb_comb {S : Type} [CommRing S] [IsLocalRing S] {x : Sp S ⟶ X} {m n : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j))
    {w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j))
    {u : Sp (DualNumber S) ⟶ t.G.left} (hu : IsTanAtG t x u) (B : Fin n → Fin m → S) (a : Fin n → S)
    (h1 : ∀ i, IsCombAtG t x v (B i) (w i)) (h2 : IsCombAtG t x w a u) :
    IsCombAtG t x v (fun k => ∑ j, a j * B j k) u := by
  obtain ⟨d, xc, hx⟩ := GlobalTheory.ShFam.EigLoc.exists_chart t x
  choose p hp using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hv j)
  choose q hq using fun j => GlobalTheory.LieLocBasis.vec_exists hx _ (hw j)
  obtain ⟨r, rfl⟩ := GlobalTheory.LieLocBasis.vec_exists hx _ hu
  obtain rfl : v = _ := funext hp
  obtain rfl : w = _ := funext hq
  simp only [GlobalTheory.LieLocBasis.comb_iff hx] at h1 h2 ⊢
  rw [h2]
  simp only [h1, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem spMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := (spMap_comp' _ _).symm

theorem dualMap_comp2 {S T U : Type} [CommRing S] [CommRing T] [CommRing U] (φ : S →+* T) (ψ : T →+* U) :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  by
    apply RingHom.ext
    intro x
    apply TrivSqZeroExt.ext <;> simp [dualMap]

end GlobalTheory.ShFam.CoordComp


open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle GlobalTheory.ShFam.CoordComp in
theorem GlobalTheory.ShFam.CoordComp.coord_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R : Type) [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (R' : Type) [CommRing R'] (φ' : c.F →+* R') (x' : Sp R' ⟶ Z.X) (g : EigFrame Z φ' x') (R'' : Type) [CommRing R''] (φ'' : c.F →+* R'') (x'' : Sp R'' ⟶ Z.X) (h : EigFrame Z φ'' x'') (ψ : R →+* R') (ψ' : R' →+* R'') (A : Mat Dw.mult R') (A' : Mat Dw.mult R''), IsLocalRing R'' → f.Coord ψ g A → g.Coord ψ' h A' → f.Coord (ψ'.comp ψ) h (A' * A.map ψ') := by
  intro E _ _ _ H Dw l Xo c O _ β Z R _ φ x f R' _ φ' x' g R'' _ φ'' x'' h ψ ψ' A A' hl h₁ h₂
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  subst a1 a2 b1 b2
  refine ⟨by rw [spMap_comp2, Category.assoc], rfl, fun τ i => ?_⟩
  have e : (fun k => spMap (dualMap (ψ'.comp ψ)) ≫ f.v τ k) =
      fun k => spMap (dualMap ψ') ≫ spMap (dualMap ψ) ≫ f.v τ k :=
    funext fun k => by rw [dualMap_comp2, spMap_comp2, Category.assoc]
  rw [e]
  exact comb_comb Z.t
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (GlobalTheory.FactorDepth.isTanAtG_map _ ψ (f.tan τ j)))
    (fun j => GlobalTheory.FactorDepth.isTanAtG_map _ ψ' (g.tan τ j)) (h.tan τ i) (fun j k => ψ' (A τ j k)) (A' τ i)
    (fun j => comb_map Z.t ψ' (a3 τ j)) (b3 τ i)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapInnerEqLambdaMulRationalVectors
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamMetric


set_option maxHeartbeats 2000000 in
theorem inner_theta_rat_eq_lam : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (p : A3.fam3.base3.Ix) a b, Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) ∈ R.Wp3 i p → ⟪D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = ((R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * ⟪D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)), D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH i t p a b hyp
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok.ok2
  have hT : ∀ c, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding c)) = Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ c)))) := by
    intro c
    rw [GlobalTheory.T.thetaMap_hilbertModel_eq_concreteThetaMap_familyThree D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH i t, CxData.tC_cpt_eq]
    show Tw.out (R.phs i • Tw.map _ (R.thG i t) (Tw.semi _ R.toRealDat.emb0 (R.jV i t) _)) = _
    have h3 := GlobalTheory.Mem.LiftForms.lvlForm_lE (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1) c
    have h3' : ((crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc).toL (R.toCx3 F).zs false i t) c = liftForm A3.A F.P0 F.ψ0 i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ c) := h3.symm
    rw [hP.phs i, one_smul]
    show R.thG i t (R.jV i t (((crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc).toL (R.toCx3 F).zs false i t) c)) = _
    exact congrArg (fun z => R.thG i t (R.jV i t z)) h3'
  have hW : (R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a) ∈ (R.toCx3 F).Wp i p := by
    show Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) ((R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a)) ∈ R.Wp3 i p
    exact (congrArg (· ∈ R.Wp3 i p) (hT a)).mpr hyp
  have hA := hR.lifts0.2 i t p a hW b
  have hL : ⟪(R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding a), (R.toCx3 F).tC (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) false i t (cpt A3.fam3.base3.v0.embedding b)⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) ⟪Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))), Y.mj.eW i (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))⟫_ℂ := by
    refine (Tw.inner_eq (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) _ _).trans ?_
    exact congrArg (cj (twAt D.what₂.embLL A3.A.v0)) (congrArg₂ (fun x y => ⟪x, y⟫_ℂ) (hT a) (hT b))
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL (Fin ((lv (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs) false).dZ i t))) ((lv (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F).zs) false).XT i t) A3.fam3.base3.v0 a b = A3.A.v0.embedding (star a ⬝ᵥ ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) *ᵥ b) := by
    have hm : metOf ((A3.A.fam.L i t).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t) A3.A.v0) = ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)).map A3.A.v0.embedding :=
      (BlockDat.XQ_herm hOk.conj (hOk.lifts i t) hOk.irr).2
    show Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((A3.A.fam.L i t).XQ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) A3.A.v0 a b = _
    rw [Formalism.L2.DIV.majAt_eq, hm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : A3.A.v0.embedding (star (a k)) = starRingEnd ℂ (A3.A.v0.embedding (a k)) := hOk.conj (a k)
    rw [hc]
    rfl
  have hU : ⟪(D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ = D.what₂.embLL (star a ⬝ᵥ ((A3.A.fam.L i t).HZ (A3.A.fam.lvlA F.P0 F.ψ0) ((A3.fam3.toSub2 (zsOf R F)).Zl i t)) *ᵥ b) := by
    have hf := (Y.formsL i t).inner (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)
    have hl := BlockDat.lf_lE_form (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (⟨hOk.conj, hOk.irr, hOk.lifts i t⟩ : BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.v0 1)
    refine hf.trans ?_
    congr 1
    exact (GlobalTheory.Mem.LiftForms.hform_mulVec (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) a b).trans (congrArg (fun M => star a ⬝ᵥ M *ᵥ b) hl)
  have hv : ∀ c, A3.A.v0.embedding c = cj (twAt D.what₂.embLL A3.A.v0) (D.what₂.embLL c) := by
    intro c
    rw [emb_eq D.what₂.embLL A3.A.v0 c, sgAt_mk _ R.hv0]
  have hN := GlobalTheory.Mem.LiftForms.inner_of_norm_sq (Y.mj.eW i) (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i) (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))) (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))
  have h1 : cj (twAt D.what₂.embLL A3.A.v0) (((RealDat.nP F.lv2 false : ℝ) : ℂ) * ⟪(D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a)))), (D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b))))⟫_ℂ) = ((RealDat.nP F.lv2 false * R.lam3 i t p A3.A.v0 : ℝ) : ℂ) * cj (twAt D.what₂.embLL A3.A.v0) ⟪(D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ a))), (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ b)))⟫_ℂ := by
    rw [← hN, ← hL, hA, hmaj, hv, hU]
    rfl
  have h2 := congrArg (cj (twAt D.what₂.embLL A3.A.v0)) h1
  rw [Links.cj_cj, map_mul, cj_ofReal, Links.cj_cj] at h2
  have hnp : ((RealDat.nP F.lv2 false : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (RealDat.nP_pos (F := F.lv2) false).ne'
  apply mul_left_cancel₀ hnp
  rw [h2]
  push_cast
  ring

end GlobalTheory.Mem.R3.LamMetric
end

