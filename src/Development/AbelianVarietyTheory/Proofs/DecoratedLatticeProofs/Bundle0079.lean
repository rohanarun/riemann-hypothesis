module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsQuotientIntegrableFoldUnimodular
section
open MeasureTheory GlobalTheory.Grow GlobalTheory.Tw
open scoped ENNReal

namespace GlobalTheory.EvalAbs

theorem lintegral_eq_of_integral {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {m₁ : Measure α} {m₂ : Measure β} {a : α → γ} {b : β → γ} (ha : Measurable a) (hb : Measurable b)
    (h : ∀ f : γ → ℂ, Measurable f → (Integrable (fun x => f (a x)) m₁ ↔ Integrable (fun y => f (b y)) m₂) ∧
      (Integrable (fun y => f (b y)) m₂ → ∫ x, f (a x) ∂m₁ = ∫ y, f (b y) ∂m₂))
    (F : γ → ℝ≥0∞) (hF : Measurable F) : ∫⁻ x, F (a x) ∂m₁ = ∫⁻ y, F (b y) ∂m₂ := by
  have e : m₁.map a = m₂.map b := by
    ext A hA
    rw [Measure.map_apply ha hA, Measure.map_apply hb hA]
    obtain ⟨h1, h2⟩ := h (A.indicator fun _ => 1) (measurable_const.indicator hA)
    have e1 : (fun x => A.indicator (fun _ => (1 : ℂ)) (a x)) = (a ⁻¹' A).indicator fun _ => 1 := rfl
    have e2 : (fun x => A.indicator (fun _ => (1 : ℂ)) (b x)) = (b ⁻¹' A).indicator fun _ => 1 := rfl
    rw [e1, e2, integrable_indicator_iff (ha hA), integrable_indicator_iff (hb hA), integrableOn_const_iff,
      integrableOn_const_iff] at h1
    rw [e1, e2, integrable_indicator_iff (hb hA), integrableOn_const_iff, integral_indicator (ha hA),
      integral_indicator (hb hA)] at h2
    simp only [enorm_eq_zero, one_ne_zero, false_or, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      Set.univ_inter, Complex.real_smul, mul_one, Complex.ofReal_inj] at h1 h2
    by_cases hf : m₂ (b ⁻¹' A) < ∞
    · exact (ENNReal.toReal_eq_toReal_iff' (h1.2 hf).ne hf.ne).1 (h2 hf)
    · rw [not_lt_top_iff.1 hf, not_lt_top_iff.1 (fun h' => hf (h1.1 h'))]
  rw [← lintegral_map hF ha, e, lintegral_map hF hb]

theorem setLIntegral_mul_right {R : Type} [Group R] [MeasurableSpace R] [MeasurableMul R] {μ : Measure R}
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup R} [Countable Γ] {𝓡 : Set R}
    (h : IsFundamentalDomain Γ 𝓡 μ) (q : R → ℝ≥0∞) (hq : ∀ γ ∈ Γ, ∀ r, q (γ * r) = q r) (m : R) :
    ∫⁻ r in 𝓡, q (r * m) ∂μ = ∫⁻ r in 𝓡, q r ∂μ := by
  have hp : MeasurePreserving (· * m) μ μ := measurePreserving_mul_right μ m
  have h2 : IsFundamentalDomain Γ ((· * m) ⁻¹' 𝓡) μ :=
    h.preimage_of_equiv hp.quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  rw [h.setLIntegral_eq h2 (fun r => q (r * m)) fun γ r => by
    rw [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hq _ γ.2 _]
  exact hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.mulRight m).measurableEmbedding q 𝓡

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {R Γ : Subgroup G} {μR : Measure R} [μR.IsHaarMeasure] [μR.IsInvInvariant] {𝓡 : Set R} {𝓑 : Set G}

theorem exists_quotientIntegrable_of_le_mean (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ) {K : G → ℝ≥0∞}
    (hK : Measurable K) (hKΓ : ∀ γ ∈ Γ, ∀ g, K (γ * g) = K g) (hfin : ∫⁻ g in 𝓑, K g ∂μ < ∞) {f : G → ℂ}
    (hf : Measurable f) (hfR : ∀ r ∈ R, ∀ g, f (r * g) = f g) (hle : ∀ h, ‖f h‖ₑ ≤ ∫⁻ r in 𝓡, K (r * h) ∂μR) :
    ∃ z, IsQuotIntL1 μR μ f z := by
  refine ⟨_, (isQuotIntL1_iff hR hf).2 ⟨hfR, ⟨(measurable_comp_out hf hfR).aestronglyMeasurable, ?_⟩, rfl⟩⟩
  obtain ⟨S, hSm, hS⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hSfd : IsFundamentalDomain Γ S μ := IsFundamentalDomain.mk' hSm.nullMeasurableSet hS
  have hSh : ∀ h : G, MeasurableSet {r : R | (r : G) * h ∈ S} := fun h =>
    (continuous_subtype_val.mul continuous_const).measurable hSm
  have e : ∀ h : G, ∫⁻ r in 𝓡, K (r * h) ∂μR = ∫⁻ r : R, S.indicator K (r * h) ∂μR := fun h => by
    have hfd : IsFundamentalDomain (Γ.subgroupOf R) {r : R | (r : G) * h ∈ S} μR :=
      IsFundamentalDomain.mk' (hSh h).nullMeasurableSet (GlobalTheory.QuotDiscrete.existsUnique_subgroupOf hΓR hS h)
    rw [h𝓡.setLIntegral_eq hfd (fun r : R => K (r * h)) fun γ r => by
      change K ((((γ : R) : G) * r) * h) = _
      rw [mul_assoc]; exact hKΓ _ γ.2 _, ← lintegral_indicator (hSh h)]
    rfl
  calc ∫⁻ c, ‖f (Quotient.out c)‖ₑ ∂quotMeas R μ μR
      ≤ ∫⁻ c, ∫⁻ r : R, S.indicator K (r * Quotient.out c) ∂μR ∂quotMeas R μ μR :=
        lintegral_mono fun c => (hle _).trans (e _).le
    _ = ∫⁻ g, S.indicator K g ∂μ := (isQuotMeasure_quotMeas hR _ (hK.indicator hSm)).symm
    _ = ∫⁻ g in 𝓑, K g ∂μ := by
        rw [lintegral_indicator hSm]
        exact hSfd.setLIntegral_eq h𝓑 K fun γ x => hKΓ _ γ.2 x
    _ < ∞ := hfin

theorem exists_quotientIntegrable_fold_unimodular (hΓR : Γ ≤ R) (hR : IsClosed (R : Set G)) [Countable Γ] [DiscreteTopology Γ]
    (h𝓡 : IsFundamentalDomain (Γ.subgroupOf R) 𝓡 μR) (h𝓑 : IsFundamentalDomain Γ 𝓑 μ)
    {U : Type} [Group U] [MeasurableSpace U] [MeasurableMul U] [MeasurableInv U] {ν : Measure U} [SFinite ν]
    [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (j : U →* G) (hj : Measurable j) (hjR : ∀ u, j u ∈ R)
    {q : G → G → ℝ≥0∞} (hq : Measurable (Function.uncurry q)) (hqΓ : ∀ γ ∈ Γ, ∀ g, ∀ r ∈ R, q (γ * g) (γ * r) = q g r)
    (hqR : ∀ r ∈ R, ∃ v, ∀ g u, q g (r * j u) = q g (j (v * u)))
    (hfin : ∫⁻ g in 𝓑, ∫⁻ u, q g (j u) ∂ν ∂μ < ∞) {P : G → ℂ} (hP : Measurable P)
    (hPR : ∀ r ∈ R, ∃ v, ∀ g u, P (j u * (r * g)) = P (j (u * v) * g))
    (hle : ∀ h, ‖P h‖ₑ ≤ ∫⁻ r in 𝓡, q (r * h) r ∂μR) :
    ∃ z, IsQuotIntL1 μR μ (fun h => ((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)) z := by
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  have : μR.IsMulRightInvariant := by rw [← Measure.inv_eq_self μR]; infer_instance
  have : ν.IsMulRightInvariant := by rw [← Measure.inv_eq_self ν]; infer_instance
  have : Countable (Γ.subgroupOf R) :=
    (Subgroup.subgroupOfEquivOfLe hΓR).toEquiv.countable_iff.2 inferInstance
  have hU : ∀ r ∈ R, ∀ g, ∫⁻ u, q g (r * j u) ∂ν = ∫⁻ u, q g (j u) ∂ν := fun r hr g => by
    obtain ⟨v, hv⟩ := hqR r hr
    simp only [hv]
    exact lintegral_mul_left_eq_self (fun u => q g (j u)) v
  refine exists_quotientIntegrable_of_le_mean hΓR hR h𝓡 h𝓑 (K := fun g => ∫⁻ u, q g (j u) ∂ν) ?_ (fun γ hγ g => ?_) hfin ?_
    (fun r hr g => ?_) fun h => ?_
  · exact (hq.comp (measurable_fst.prodMk (hj.comp measurable_snd))).lintegral_prod_right'
  · rw [← hU γ⁻¹ (inv_mem (hΓR hγ)) g]
    refine lintegral_congr fun u => ?_
    rw [← hqΓ γ hγ g _ (mul_mem (inv_mem (hΓR hγ)) (hjR u)), mul_inv_cancel_left]
  · refine Complex.measurable_ofReal.comp (StronglyMeasurable.measurable ?_)
    exact (hP.comp ((hj.comp measurable_snd).mul measurable_fst)).norm.stronglyMeasurable.integral_prod_right'
  · obtain ⟨v, hv⟩ := hPR r hr
    simp only [hv]
    rw [integral_mul_right_eq_self (fun u => ‖P (j u * g)‖) v]
  · have hm : Measurable fun p : U × R => q (p.2 * h) (p.2 * j p.1⁻¹) :=
      hq.comp (((measurable_subtype_coe.comp measurable_snd).mul_const h).prodMk
        ((measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst.inv)))
    calc ‖((∫ u, ‖P (j u * h)‖ ∂ν : ℝ) : ℂ)‖ₑ = ‖∫ u, ‖P (j u * h)‖ ∂ν‖ₑ := by
          simp [eNorm_eq_nnNorm]
      _ ≤ ∫⁻ u, ‖‖P (j u * h)‖‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ u, ∫⁻ r in 𝓡, q (r * h) (r * j u⁻¹) ∂μR ∂ν := by
          refine lintegral_mono fun u => ?_
          rw [enorm_norm]
          refine (hle _).trans (le_of_eq ?_)
          rw [← setLIntegral_mul_right h𝓡 (fun r : R => q (r * h) (r * j u⁻¹)) (fun γ hγ r => by
            simp only [Subgroup.coe_mul, mul_assoc]
            exact hqΓ _ hγ _ _ (mul_mem r.2 (hjR _))) ⟨j u, hjR u⟩]
          simp only [Subgroup.coe_mul, mul_assoc, map_inv, mul_inv_cancel, mul_one]
      _ = ∫⁻ r in 𝓡, ∫⁻ u, q (r * h) (r * j u⁻¹) ∂ν ∂μR := lintegral_lintegral_swap hm.aemeasurable
      _ = _ := by
          refine lintegral_congr fun r => ?_
          rw [lintegral_inv_eq_self (μ := ν) fun u => q (r * h) (r * j u), hU r r.2]

end

end GlobalTheory.EvalAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentFiniteAdelesIffFrameUnipotentRadiStatement
section
open Matrix NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlagUnipotent_finiteAdeles_iff_frame_unipotentRadical : ∀ (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔ ((∀ a : Fin ρ, (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I (x a) ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) '' {b | b.1 < a.1})) ∧ (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) ∧ ∀ y : Formalism.L2.SG.HidaSetting.VA I, (∀ a, Formalism.L2.SG.HidaSetting.hA I (Formalism.L2.SG.HidaSetting.incl I (x a)) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b))) := by
  first | exact @GlobalTheory.UnipFin.unip_flag_iff_Nfin | exact GlobalTheory.UnipFin.unip_flag_iff_Nfin | (intros; apply GlobalTheory.UnipFin.unip_flag_iff_Nfin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelFiniteDatumBoundedLevelSize
section
noncomputable section

namespace GlobalTheory.Core.Ht2.LastDatumS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder
open GlobalTheory.TopStep GlobalTheory.ColNorms.LastDatum

theorem smallDatum_xiCpl2_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : RowPt Pr N.R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N, SmallDatum (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hY
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hI := H.2.2.2.2.2.2.1
  have hT : TilOk Pr sel mu u := by
    refine tilOk_of hPr u fun P hP => ?_
    have hmu : mu = mu0 X.F X.E X.K Sg := H.2.2.2.2.1
    rw [hmu, twistPrimes_trivialTuple_empty sel Sg] at hP
    simp at hP
  have key := EntryDatum.smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 (tilQ sel mu u d).1 (tilQ sel mu u d).2
    (frsF sel mu p) (tilFr hT d) (frsF_mem p) (fun P => (tilFr_isLiftFr hT d P).1)
    (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P y => locTop Ch sel mu cst (N.R.m - 2) P y ((frsF sel mu p P).symm (repY Y))) (fun _ => 1)
    (fun P => locSmall_locTop hI.hm hI.cst_ok H.2.2.2.2.2.1 (h1 P.1 P.2) (repY_int p hY (h1 P.1 P.2)))
  rw [Finset.prod_const_one] at key
  convert key using 1
  funext x
  unfold XiCpl2
  simp only [locTop_tilFr]

end GlobalTheory.Core.Ht2.LastDatumS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryFiniteDatumBoundedLevelSize
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.EntryDatumS

open GlobalTheory.ColNorms.EntryDatum

theorem smallDatum_xiEntry_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.Core.Ht2.UnfoldS.locSmall_XiAt_sharp
  refine ⟨C, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p' => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hg : ∀ i, Pr.g i = N.g i := H.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (p : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j p P x
    have hP := h1 P.1 P.2
    unfold frsF
    rw [dite_eq_left hP]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ p.deco ⟨P.1, hP⟩).1 x
  have key := smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 p'.deco.1 p'.deco.2 (frsF sel mu p) (frsF sel mu p')
    (hfr p) (hfr p') (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P => XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) _
    (hC CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be)
  have e : ∏ P : rowSG Pr sel mu, (Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2) =
      ((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    rw [Finset.prod_pow, ← Nat.cast_prod, h4, hg 0, hg 1]
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [e] at key
  exact key

end GlobalTheory.Core.Ht2.EntryDatumS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHarishChandraParamRevEqWeylWeightTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.TopParam

def Dset (R : Ranks) (h : HCParam R) : Finset ℚ :=
  (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)) ∪
    Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)

theorem sgHC_sub_mem (R : Ranks) (h : HCParam R) (i : ℕ) (hi : i < R.N R.m - 1) :
    sgHC R h i - (R.m * (R.t + 1) / 2 : ℚ) ∈ Dset R h := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold sgHC Dset
  simp only [add_sub_cancel_left]
  split_ifs with h1 h2 h3
  · simp
  · apply Finset.mem_union_left; apply Finset.mem_union_right; simp
  · apply Finset.mem_union_right
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, TPar.block, Finset.mem_image, Finset.mem_range]
    refine ⟨⟨_, h2⟩, (i - (R.k - 1)) % (R.t + 1) - 1, ?_, ?_⟩
    · have := Nat.mod_lt (i - (R.k-1)) (show 0 < R.t + 1 by omega); omega
    · have : 1 ≤ (i - (R.k - 1)) % (R.t + 1) := Nat.pos_of_ne_zero h3
      push_cast [Nat.cast_sub this]; ring
  · exfalso; apply h2
    unfold Ranks.N at hi
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
    generalize R.m * (R.t + 1) = P at hi
    omega

theorem card_Dset_le (R : Ranks) (h : HCParam R) : (Dset R h).card ≤ R.N R.m - 1 := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold Dset
  calc _ ≤ (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)).card
          + (Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)).card := Finset.card_union_le _ _
    _ ≤ ((R.k - 1) + R.m) + R.m * R.t := by
        gcongr
        · refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
          · exact Finset.card_image_le.trans (by simp)
          · exact Finset.card_image_le.trans (by simp)
        · refine (Finset.card_biUnion_le_card_mul _ _ R.t ?_).trans (by simp)
          intro j _
          exact Finset.card_image_le.trans (by simp)
    _ = R.N R.m - 1 := by
        unfold Ranks.N
        have : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
        rw [this]; omega

end GlobalTheory.Core.Rk.TopParam

namespace GlobalTheory.Core.Rk.TopParam

theorem neg_lam_rev_eq : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → ∀ τ (i : Fin D.sp.X'.rank), -M.lam τ (Fin.rev i) = (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℝ) + ((rhoVec D.sp.X'.rank i : ℚ) : ℝ) := by
  intro D u M hsg τ i
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hdiv : ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℚ) = (D.R.m : ℚ) * (D.R.t + 1) / 2 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rw [Nat.cast_div (by rw [ha]; exact Dvd.intro (a * (D.R.t + 1)) (by ring)) (by norm_num)]
    push_cast; ring
  have hn : ((D.sp.X'.rank : ℕ) : ℚ) = ((D.R.N D.R.m - 1 : ℕ) : ℚ) := by rw [rankP D]
  let F : Fin D.sp.X'.rank → ℚ := fun i =>
    sgHC D.R (D.hcW u τ) (Fin.cast (rankP D) i) - (D.R.m * (D.R.t + 1) / 2 : ℚ)
  let G : Fin D.sp.X'.rank → ℚ := fun i => -q (Fin.rev i)
  have hRHS : ∀ i : Fin D.sp.X'.rank,
      (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℚ) + rhoVec D.sp.X'.rank i = F i := by
    intro i
    have h1 := hsg (Fin.cast (rankP D) i) τ
    simp only [sgT, shW, F]
    rw [Int.cast_sub, h1, Int.cast_natCast, hdiv]
    simp only [rhoVec, Fin.coe_cast]
    rw [hn]; ring
  have hFa : StrictAnti F := by
    intro i j hij
    rw [← hRHS i, ← hRHS j]
    have h1 : (sgT u τ).w (Fin.cast (rankP D) j) ≤ (sgT u τ).w (Fin.cast (rankP D) i) :=
      (sgT u τ).anti (by rw [Fin.le_iff_val_le_val]; simp only [Fin.coe_cast]; exact hij.le)
    have h2 : rhoVec D.sp.X'.rank j < rhoVec D.sp.X'.rank i := by
      simp only [rhoVec]; have : (i : ℚ) < j := by exact_mod_cast hij
      linarith
    have h1' : ((sgT u τ).w (Fin.cast (rankP D) j) : ℚ) ≤ (sgT u τ).w (Fin.cast (rankP D) i) := by exact_mod_cast h1
    linarith
  have hGa : StrictAnti G := by
    intro i j hij
    have h1 := hanti (Fin.rev_lt_rev.mpr hij)
    rw [hq, hq] at h1
    have h1' : q (Fin.rev i) < q (Fin.rev j) := by exact_mod_cast h1
    simp only [G]; linarith
  have hFm : ∀ x, F x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have := sgHC_sub_mem D.R (D.hcW u τ) (Fin.cast (rankP D) x) (Fin.cast (rankP D) x).isLt
    simpa [F] using this
  have hGm : ∀ x, G x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have hmem : (q (Fin.rev x), M.ε τ (Fin.rev x)) ∈ parB (Ptw D) D.R.m τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.mpr D.R.m_even
    simp only [parB, dualPar, TPar.Dpar, Finset.mem_image, hodd, if_false, add_zero] at hmem
    obtain ⟨⟨y1, y2⟩, ⟨⟨z1, z2⟩, hz, hzy⟩, hy⟩ := hmem
    simp only [Prod.mk.injEq] at hzy hy
    obtain ⟨rfl, rfl⟩ := hzy
    have hGx : G x = z1 := by simp only [G]; rw [← hy.1]; ring
    rw [hGx]
    simp only [Dset, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Prod.mk.injEq, D.hcW_v, D.hcW_b, D.hcW_e] at hz ⊢
    rcases hz with (⟨a, ha, -⟩ | ⟨a, ha, -⟩) | ⟨a, -, w, hw, hwz, -⟩
    · exact Or.inl (Or.inl ⟨a, ha⟩)
    · exact Or.inl (Or.inr ⟨a, ha⟩)
    · exact Or.inr ⟨a, hwz ▸ hw⟩
  have hcard : (Dset D.R (D.hcW u τ)).card = D.sp.X'.rank := by
    apply le_antisymm
    · rw [rankP D]; exact card_Dset_le _ _
    · have hsub : Finset.univ.image F ⊆ Dset D.R (D.hcW u τ) := by
        intro y hy; obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy; exact hFm x
      have := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ hFa.injective, Finset.card_univ, Fintype.card_fin] at this
  have hFG : F ∘ Fin.rev = G ∘ Fin.rev := by
    have e1 := Finset.orderEmbOfFin_unique hcard (f := F ∘ Fin.rev) (fun x => hFm _)
      (fun a b hab => hFa (Fin.rev_lt_rev.mpr hab))
    have e2 := Finset.orderEmbOfFin_unique hcard (f := G ∘ Fin.rev) (fun x => hGm _)
      (fun a b hab => hGa (Fin.rev_lt_rev.mpr hab))
    exact e1.trans e2.symm
  have hi := congrFun hFG (Fin.rev i)
  simp only [Function.comp, Fin.rev_rev, G] at hi
  rw [hq]
  have key := congrArg (fun x : ℚ => (x : ℝ)) ((hRHS i).trans hi)
  push_cast at key
  rw [key]

end GlobalTheory.Core.Rk.TopParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RatEquiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RatPtsEquiv

theorem rat_equiv : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), ∃ r : ↥(GQ V) ≃* ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))), ∀ γ, finM V hn γ.1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1).1 := by
  intro D V n hn
  subst hn
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  have hm : ∀ δ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))),
      bc (incA D) δ.1 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    intro δ
    have hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1.1 * V.gram * δ.1.1 = V.gram := δ.2
    have h2 := congrArg (fun M => M.map (incA D)) hδ'
    simp only [Matrix.map_mul] at h2
    exact h2
  let φ : ↥(UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl))) →* ↥(GQ V) :=
    { toFun := fun δ => ⟨⟨bc (incA D) δ.1, hm δ⟩, Subgroup.mem_subgroupOf.2 ⟨δ.1, δ.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        exact map_one (bc (incA D))
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext
        exact map_mul (bc (incA D)) a.1 b.1 }
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      have h1 : (bc (incA D) a.1 : GL (Fin V.rank) _) = bc (incA D) b.1 := congrArg (fun x => x.1.1) h
      apply Subtype.ext; apply Units.ext
      refine Matrix.ext fun i j => ?_
      have := congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) h1
      exact hinj this
    · intro γ
      obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 γ.2
      exact ⟨⟨δ, hδ⟩, Subtype.ext (Subtype.ext e)⟩
  refine ⟨(MulEquiv.ofBijective φ hφ).symm, fun γ => ?_⟩
  set δ := (MulEquiv.ofBijective φ hφ).symm γ with hδ
  have hγ : γ = φ δ := by
    rw [hδ]; exact ((MulEquiv.ofBijective φ hφ).apply_symm_apply γ).symm
  rw [hγ]
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  rfl

end GlobalTheory.RatPtsEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParame
section
noncomputable section

namespace GlobalTheory.SatBc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem satU_eq_of_bcParam_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂˣ,
      GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α' →
      ∀ φ ∈ Hecke ℂ (KU σ n), SatU ϖ q φ (fun i => (α i : ℂ)) = SatU ϖ q φ (fun i => (α' i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU α α' e φ hφ
  have e1 := congrArg (Multiset.map fun z : ℂˣ => (z : ℂ)) (add_right_cancel e)
  refine GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq _ (SatU ϖ q φ)
    (fun γ hγ => GlobalTheory.SatakeWeyl.satWeyl L ϖ σ q n (n / 2) hU (by omega) (by omega) γ hγ φ hφ) _ _
    (fun i => (α i).ne_zero) ?_
  simpa [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBc
end
end

