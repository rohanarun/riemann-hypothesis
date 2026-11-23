module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicLeviDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0510
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatrixDiagonalizable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrExhaust

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter _root_.Topology
open PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_pow_mul_mem {v : HeightOneSpectrum (𝓞 F)} {ϖ : Fv F v} (h : ‖ϖ‖ < 1) (c : Fv F v) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k * c ∈ v.adicCompletionIntegers F := by
  have h0 : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k * ‖c‖) atTop (𝓝 (0 * ‖c‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h).mul_const _
  rw [zero_mul] at h0
  filter_upwards [h0.eventually (gt_mem_nhds one_pos)] with k hk
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_mul, norm_pow]
  exact hk.le

theorem eventually_smul_mem {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
    {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ} (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v ⊗[F] E) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k • x ∈ S := by
  have h : ∀ᶠ k : ℕ in atTop, ∀ i, ϖ ^ k * (Algebra.TensorProduct.basis (Fv F v) bs).repr x i ∈
      v.adicCompletionIntegers F :=
    eventually_all.2 fun i => eventually_pow_mul_mem hG.unif_lt _
  filter_upwards [h] with k hk
  have hmem : ϖ ^ k • x ∈ (S : Set (Fv F v ⊗[F] E)) := by
    rw [hG.carrier]
    intro i
    simpa [map_smul] using hk i
  exact hmem

theorem exhaust : Exhaust := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG b
  have h : ∀ᶠ k : ℕ in atTop, ∀ a c, ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈ S :=
    eventually_all.2 fun a => eventually_all.2 fun c => eventually_smul_mem hG _
  obtain ⟨k, hk⟩ := h.exists
  have hX : PositivityTheory.PfSWUS.Loc.cT σS (Matrix.of fun a c => (⟨_, hk a c⟩ : S)) = Matrix.of fun a c => (⟨_, hk a c⟩ : S) := by
    ext a c
    have hb := b.2 a c
    simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hG.sig]
    simp only [sigR_smul]
    exact congrArg _ hb
  refine ⟨k, _, hX, ?_⟩
  apply Subtype.ext
  funext a c
  show (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c = (ϖ ^ k)⁻¹ • ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hG.unif_ne), one_smul]

end GlobalTheory.CompanionTheory.GunrExhaust

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassSecond
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.LocPhiUnit

section Fixed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
  (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

theorem exists_inclPlus_half (z : k ⊗[maximalRealSubfield E] Fld Q) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q,
      inclPlus Q k a = ((1 : k) ⊗ₜ[maximalRealSubfield E] (2⁻¹ : Fld Q)) * (z + involBase Q k z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s y =>
    refine ⟨s ⊗ₜ ⟨(y + invol Q y) / 2, ?_⟩, ?_⟩
    · change invol Q _ = _
      simp only [map_div₀, map_add (f := _), invol_invol, map_ofNat, AlgHom.id_apply, add_comm]
    · change s ⊗ₜ[maximalRealSubfield E] ((y + invol Q y) / 2) = _ * (s ⊗ₜ y + s ⊗ₜ invol Q y)
      rw [← TensorProduct.tmul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_inv_mul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [map_add (f := _), ha, hb, map_add (f := _)]
    ring

theorem exists_inclPlus_of_fixed {z : k ⊗[maximalRealSubfield E] Fld Q} (hz : involBase Q k z = z) :
    ∃ a : k ⊗[maximalRealSubfield E] plus Q, inclPlus Q k a = z := by
  obtain ⟨a, ha⟩ := exists_inclPlus_half Q k z
  refine ⟨a, ?_⟩
  have h2 : (2 : k ⊗[maximalRealSubfield E] Fld Q) = (1 : k) ⊗ₜ[maximalRealSubfield E] (2 : Fld Q) :=
    (map_ofNat (Algebra.TensorProduct.includeRight :
      Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q) 2).symm
  rw [ha, hz, ← two_mul, ← mul_assoc, h2, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    inv_mul_cancel₀ two_ne_zero, ← Algebra.TensorProduct.one_def, one_mul]

theorem inclPlus_injective : Function.Injective (inclPlus Q k) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := k) (plus Q).val.toLinearMap
    Subtype.val_injective

theorem exists_unit_of_fixed {y : k ⊗[maximalRealSubfield E] Fld Q} (hu : IsUnit y)
    (hy : involBase Q k y = y) :
    ∃ x : (k ⊗[maximalRealSubfield E] plus Q)ˣ,
      inclPlus Q k (x : k ⊗[maximalRealSubfield E] plus Q) = y := by
  obtain ⟨u, rfl⟩ := hu
  have hinv : involBase Q k ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) :
      k ⊗[maximalRealSubfield E] Fld Q) = (u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) := by
    have h1 : (u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
        ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) = 1 := by
      conv_lhs => rw [← hy]
      rw [← map_mul, Units.mul_inv, map_one]
    calc _ = ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q) *
          ((u : k ⊗[maximalRealSubfield E] Fld Q) * involBase Q k
            ((u⁻¹ : (k ⊗[maximalRealSubfield E] Fld Q)ˣ) : k ⊗[maximalRealSubfield E] Fld Q)) := by
          rw [Units.inv_mul_cancel_left]
      _ = _ := by rw [h1, mul_one]
  obtain ⟨a, ha⟩ := exists_inclPlus_of_fixed Q k hy
  obtain ⟨b, hb⟩ := exists_inclPlus_of_fixed Q k hinv
  have hab : a * b = 1 := inclPlus_injective Q k (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Fixed

section Matrix

theorem aeval_mul_of_intertwine {K : Type} [Field K] {n : ℕ} {B C H : Matrix (Fin n) (Fin n) K}
    (h : B * H = H * C) (g : K[X]) : aeval B g * H = H * aeval C g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial d a =>
    have e : B ^ d * H = H * C ^ d :=
      (((show SemiconjBy H C B from h.symm).pow_right d).eq).symm
    rw [aeval_monomial, aeval_monomial]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_assoc, e]

theorem cT_mul {K : Type} [Field K] (s : K →+* K) {n : ℕ} (B C : Matrix (Fin n) (Fin n) K) :
    cT s (B * C) = cT s C * cT s B := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

end Matrix

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem involBase_locPhi (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v)
    {r : ℕ} (Q : SelfRecip E r) {r₀ : E[X]} (hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0)
    (f : (w.adicCompletion E)[X]) :
    involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q f) =
      locPhi hU w hw v hv Q ((f.map (cj w)).comp (atPl w r₀)) := by
  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (inclBase Q k).toRingHom.comp (locJ hU w hw v hv).toRingHom
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (locJ hU w hw v hv y)) =
      inclBase Q k (locJ hU w hw v hv (cj w y))
    rw [locJ_cj]
    generalize locJ hU w hw v hv y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (involBase Q k).toRingHom
  have hR : locPhi hU w hw v hv Q (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [locPhi_atPl]
    congr 1
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at hr
    exact eq_inv_of_mul_eq_one_right hr
  have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
  have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    change (1 : k) ⊗ₜ invol Q (alpha Q) = _
    rw [invol_alpha]
  change ib (eval₂ ι _ f) = eval₂ ι _ _
  rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
  exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm

end Local

theorem locPhi_mem_units_plus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ hH hdet h3 m hM hMdet r Q hQ
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hr : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
  obtain ⟨A, hA⟩ : ∃ A, A = γ₀.val.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H, H = H₀.map (algebraMap E (w.adicCompletion E)) := ⟨_, rfl⟩
  rw [← hA, ← hHd] at hM hMdet
  obtain ⟨M, hMd⟩ : ∃ M, M = aeval A m := ⟨_, rfl⟩
  rw [← hMd] at hM hMdet
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ₀.val.charpoly := by rw [hA]; exact Matrix.charpoly_map _ _
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hHh : cT (cj w) H = H := by
    rw [hHd, ← cT_map hU w hw]
    exact congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hH
  have hcA : cT (cj w) A * H * A = H := by
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h3
    simp only [Matrix.map_mul, cT_map hU w hw] at this
    rw [hA, hHd]
    exact this
  have hint : cT (cj w) A * H = H * aeval A (atPl w r₀) := by
    calc cT (cj w) A * H = cT (cj w) A * H * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = H * aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA]
  have hH0 : IsUnit H := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at *
    exact (left_ne_zero_of_mul hMdet).isUnit
  have hM0 : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [Matrix.det_mul] at hMdet
    exact (right_ne_zero_of_mul hMdet).isUnit
  have hfix : M = aeval A ((m.map (cj w)).comp (atPl w r₀)) := by
    have h1 : cT (cj w) M * H = H * M := by
      have := hM
      rw [IsHerm, cT_mul, hHh] at this
      exact this
    rw [hMd, GlobalTheory.NormInert.cT_aeval, aeval_mul_of_intertwine hint, ← aeval_comp, ← hMd] at h1
    exact (hH0.mul_left_cancel h1).symm
  have hdiv : A.charpoly ∣ (m.map (cj w)).comp (atPl w r₀) - m :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by rw [map_sub, ← hfix, ← hMd, sub_self])
  have hΦ0 : locPhi hU w hw v hv Q A.charpoly = 0 := by
    rw [hAP, locPhi_atPl]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  have hy : involBase Q (v.adicCompletion (maximalRealSubfield E)) (locPhi hU w hw v hv Q m) =
      locPhi hU w hw v hv Q m := by
    obtain ⟨t, ht⟩ := hdiv
    rw [involBase_locPhi hU w hw v hv Q hr, ← sub_eq_zero, ← map_sub, ht, map_mul, hΦ0, zero_mul]
  obtain ⟨u, hu⟩ := hM0
  have hcomm : Commute A (u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hu, hMd]
    have := congrArg (aeval A) (mul_comm (X : (w.adicCompletion E)[X]) m)
    rw [map_mul, map_mul, aeval_X] at this
    exact this
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A
    ((u⁻¹ : (Matrix (Fin n) (Fin n) (w.adicCompletion E))ˣ) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    hAsep hcomm.units_inv_right.eq
  have hdiv2 : A.charpoly ∣ m * g - 1 :=
    GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ (by
      rw [map_sub, map_mul, ← hg, ← hMd, ← hu, Units.mul_inv, map_one, sub_self])
  have hone : locPhi hU w hw v hv Q m * locPhi hU w hw v hv Q g = 1 := by
    obtain ⟨t, ht⟩ := hdiv2
    rw [← map_mul, ← sub_eq_zero, ← map_one (locPhi hU w hw v hv Q), ← map_sub, ht, map_mul, hΦ0,
      zero_mul]
  exact exists_unit_of_fixed Q _ (isUnit_iff_exists_inv.2 ⟨_, hone⟩) hy

end GlobalTheory.CompanionTheory.LocPhiUnit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThird
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

noncomputable section

namespace GlobalTheory.CompanionTheory.NormCongr

theorem mem_norms_locPhi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
  intro E _ _ _ hU w hw v hv n γ₀ hell H₀ _ hdet hinv m c hc1 hc2 r Q hQ x hx
  exact mem_norms_of_congr_equiv hU w hw (v.adicCompletion (maximalRealSubfield E)) (locJ hU w hw v hv)
    (locJ_algebraMap hU w hw v hv) (locJ_cj hU w hw v hv) n γ₀ hell H₀ hdet hinv m c hc1 hc2 r Q hQ x hx

end GlobalTheory.CompanionTheory.NormCongr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompact
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem levi_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ C ⊆ leviMin σ J X Y ∩ minParOne σ J X ∧ ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∃ δ ∈ ratPts σ J, δ ∈ leviMin σ J X Y ∧ ∃ c ∈ C, m = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨L, hL, hLc⟩ := _root_.GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup F E σ h n J hJ r X Y hW
  have hmem : ∀ g, g ∈ L ↔ g ∈ leviMin σ J X Y ∧ g ∈ minParOne σ J X := fun g => by
    rw [← SetLike.mem_coe, hL]; rfl
  obtain ⟨ε, hε, hh⟩ := GlobalTheory.T.idele_bound_of_joint_anisotropic F E σ h n J hJ _ (hermFam σ J X Y) (L : Set (GAd σ J))
    (_root_.GlobalTheory.CompanionTheory.ParCocompact.hermFam_nondeg F E σ h n J hJ r X Y hW)
    (fun g hg j => GlobalTheory.T.levi_minimal_idele_hermitian_bound F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 ((hmem g).1 hg).2 j)
  obtain ⟨Ω, hΩ, hsub, hred⟩ := GlobalTheory.T.commutant_closed_subgroup_compact_quotient F E σ h n J hJ _ (projFam σ J X Y) L hLc
    (fun g hg k => GlobalTheory.T.levi_minimal_commutes_projection_family F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 k) ⟨ε, hε, hh⟩
    (fun γ hγ hc => (hmem γ).2 (GlobalTheory.T.mem_levi_minimal_of_commutes_projections F E σ h n J hJ r X Y hW γ hγ hc))
  refine ⟨Ω, hΩ, fun c hc => (hmem c).1 (hsub hc), fun m hm hm1 => ?_⟩
  obtain ⟨δ, hδ, hδL, hd⟩ := hred m ((hmem m).2 ⟨hm, hm1⟩)
  exact ⟨δ, hδ, ((hmem δ).1 hδL).1, _, hd, by group⟩

theorem minParOne_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨hcl, hmul⟩ := minParOne_props h hJ hW
  obtain ⟨C, hC, hU⟩ := GlobalTheory.CompanionTheory.UnipCocompact.unipMin_cocompact F E σ h n J hJ r X Y hW
  obtain ⟨C', hC', hsub, hM⟩ := levi_cocompact F E σ h n J hJ r X Y hW
  refine ⟨(C ∩ minParOne σ J X) * C', (hC.inter_right hcl).mul hC', ?_, fun p hp => ?_⟩
  · rintro _ ⟨c, hc, c', hc', rfl⟩
    exact hmul _ hc.2 _ (hsub hc').2
  · obtain ⟨u, hu, m, hm, hm1, rfl⟩ := _root_.GlobalTheory.CompanionTheory.LeviDecomp.levi_decomp F E σ h n J hJ r X Y hW p hp
    obtain ⟨δ, hδ, hδL, c', hc', rfl⟩ := hM m hm hm1
    have hu' := GlobalTheory.T.levi_normalizes_unipotent_ter F E σ h n J hJ r X Y hW δ hδL u hu
    obtain ⟨δ', hδ', hδU, c, hc, hcU, e⟩ := hU _ hu'
    refine ⟨δ * δ', mul_mem hδ hδ', mul_mem_minPar (leviMin_subset X Y hδL)
      (minParOne_subset (unipMin_subset_minParOne X hδU)), c * c',
      ⟨c, ⟨hc, unipMin_subset_minParOne X hcU⟩, c', hc', rfl⟩, ?_⟩
    have e2 : u = δ * (δ' * c) * δ⁻¹ := by
      rw [← e]; group
    rw [e2]; group

end GlobalTheory.CompanionTheory.ParCocompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormula
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.MixZ

theorem curveInt : CurveInt := by
  intro Z _ q hq L M r hr
  refine ⟨fun σ => ?_, GlobalTheory.ArchDimZero.main ℤ Z q hq M L r hr⟩
  have := GlobalTheory.ArchDimZero.isProper hq
  have := GlobalTheory.ArchDimZero.finite_cxPts hq σ
  have h₁ : (L.φ σ).chernPart 0 1 = Measure.count := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ 1 y, Measure.count_singleton]
    simp
  have h₂ : (L.φ σ).chernPart 0 (-1) = 0 := Measure.ext_iff_singleton.2 fun y => by
    rw [GlobalTheory.ArchDimZero.chernPart_singleton hq L σ (-1) y]
    simp
  refine ⟨?_, ?_⟩
  · rw [h₁]
    exact (Integrable.of_finite (μ := Measure.count) (f := logNorm (M.φ σ) r)).integrableOn
  · rw [h₂]
    exact (integrable_zero_measure : Integrable (logNorm (M.φ σ) r) 0).integrableOn

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula
section
noncomputable section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.SiegLoc

namespace GlobalTheory.CompanionTheory.GunrNu

theorem card_range_pow {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    (hR : IsUnrQuad R σ ϖ q ε) (k : ℕ) (d : R) (hd : σ d = d) :
    ∃ e : ℕ, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) =
      (q ^ 2) ^ e := by
  rcases Scaled.fixed_decomp hR k d hd with h0 | ⟨a₀, e, c, rfl, hc, hc1, rfl⟩
  · have hz : Ideal.Quotient.mk (lev ϖ k) d = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h0
    have hr : (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = {0} := by
      ext z
      simp [hz]
    exact ⟨0, by rw [hr]; simp⟩
  · exact ⟨e, by
      rw [Scaled.card_range_mul hR.reg (hR.fixLocal c hc hc1) e a₀,
        _root_.GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε hR e, pow_mul]⟩

theorem nuPow : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  intro R _ σ ϖ q ε hR n k B hB
  obtain ⟨h, hh, rfl⟩ := hB
  have hq := hR.one_lt
  have hfin : Finite (R ⧸ lev ϖ k) := Nat.finite_of_card_ne_zero (by
    rw [_root_.GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε hR k]
    exact pow_ne_zero _ (by omega))
  let _ : Fintype (R ⧸ lev ϖ k) := Fintype.ofFinite _
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := _root_.GlobalTheory.CompanionTheory.HermDiag.herm_diag R σ ϖ q ε hR n h hh
  choose eI hcard using fun i => card_range_pow hR k (d i) (hd i)
  have hnu : nuAt ϖ (red ϖ k h) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [_root_.GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd,
      Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow (Nat.one_lt_pow (by norm_num) hq)]

end GlobalTheory.CompanionTheory.GunrNu

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbitStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_eq_iff_same_torus_orbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y y' : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder (PtsOver.map i rfl _ y) z → IsUnder (PtsOver.map i rfl _ y') z' → (y = y' ↔ SameOrbit z z') := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | exact GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit | (intros; apply GlobalTheory.CompanionTheory.MixZ.Orbit.eq_iff_sameOrbit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_irreducible_finite_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), HasFiniteLength (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.ProdFL.main | exact GlobalTheory.CompanionTheory.ProdFL.main | (intros; apply GlobalTheory.CompanionTheory.ProdFL.main <;> assumption)
end

