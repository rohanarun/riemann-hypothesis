module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicComponentProductOfSmoothReps
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0011
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsScalarOfTwistedIntertwinerCommutingAlgebra
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0008
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalEigenspaceInfFixedOffNCMDatum
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section One
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem mem_eigL' (w : Pl K) (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ) (v : LL μ) :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply]

private theorem mem_fixL' (w : Pl K) (J : Subgroup (Gw n w)) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply,
    Subgroup.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, rhoL]

private theorem rhoL_comm {w w' : Pl K} (hne : w' ≠ w) (g : Gw n w) (x : Gw n w') (v : LL μ) :
    rhoL μ w' x (rhoL μ w g v) = rhoL μ w g (rhoL μ w' x v) := by
  have h := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' hne g x
  simp only [rhoL, rhoF]
  rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, ← map_mul, ← map_mul, h]

end One

private theorem kerChr_co {G : Type} [Group G] [TopologicalSpace G] {J : Subgroup G} {χ : G → ℂ} (hJ : CO J) (h : IsChr J χ) :
    CO (kerChr J χ h) := by
  have e : (kerChr J χ h : Set G) = (J : Set G) ∩ χ ⁻¹' {1} := rfl
  have ho : IsOpen (χ ⁻¹' {(1 : ℂ)}) := h.1.isOpen_fiber 1
  have hc : IsClosed (χ ⁻¹' {(1 : ℂ)}) := isClosed_singleton.preimage h.1.continuous
  rw [CO, e]
  exact ⟨hJ.1.inter_right hc, hJ.2.inter ho⟩

private theorem exists_ext {A ι : Type*} {B : A → Type*} (f : ι → A) (hf : Function.Injective f) (U : ∀ i, B (f i))
    (d : ∀ a, B a) : ∃ U' : ∀ a, B a, (∀ i, U' (f i) = U i) ∧ ∀ a, a ∉ Set.range f → U' a = d a := by
  have key : ∀ (i j : ι) (hj : f j = f i), (hj ▸ U j : B (f i)) = U i := by
    intro i j hj
    obtain rfl := hf hj
    rfl
  refine ⟨fun a => if h : ∃ i, f i = a then h.choose_spec ▸ U h.choose else d a, fun i => ?_, fun a ha => dif_neg ha⟩
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  simp only [dif_pos h]
  exact key i _ _

section Two
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q}
variable (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]

private theorem under_of_over {v : Pl F} (u : PlacesOver E v) : u.1.under (𝓞 F) = v := by
  ext1
  exact (Ideal.over_def u.1.asIdeal v.asIdeal).symm

private theorem finite_over (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
  subst hw
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem mem_Zv (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (O : LL μ →L[ℂ] LL μ) (x : ℝ) (v : LL μ) :
    v ∈ eigIn (V ⊓ offN μ T) O x ↔ v ∈ V ∧ (∀ w : Pl E, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → v ∈ eigL μ w (T.J w) (T.χ w)) ∧
      O v = (x : ℂ) • v := by
  simp only [eigIn, offN, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe,
    and_assoc]

private theorem Zv_closed (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)) (hV : IsClosed (V : Set (LL μ))) (O : LL μ →L[ℂ] LL μ) (x : ℝ) :
    IsClosed (eigIn (V ⊓ offN μ T) O x : Set (LL μ)) := by
  have e : (eigIn (V ⊓ offN μ T) O x : Set (LL μ)) = (V : Set (LL μ)) ∩ ((⋂ w, ⋂ (_ : w.under (𝓞 F) ∉ (nsS T : Set (Pl F))),
      (eigL μ w (T.J w) (T.χ w) : Set (LL μ))) ∩ {v | O v = (x : ℂ) • v}) := by
    ext v
    simp only [SetLike.mem_coe, mem_Zv, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine hV.inter (IsClosed.inter ?_ (isClosed_eq O.continuous (continuous_const_smul _)))
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) (T.χ w) (T.co w) (T.chr w)).1

end Two

theorem UpperTheory.finiteDimensional_eigenspace_inf_fixed_offN_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]
        (ν : Measure (archGroup E n)) [ν.IsHaarMeasure] (a : TI E n) (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀)
        (V : Submodule ℂ (LL μ)), IsSummand μ V → (∀ v ∈ nsS T, ∀ u : PlacesOver E v, u = T.mk' v) → ∀ x : ℝ, x ≠ 0 →
          IsClosed (eigIn (V ⊓ offN μ T) (Oinf μ ν a) x : Set (LL μ)) ∧
          (∀ v ∈ nsS T, ∀ g, ∀ f ∈ eigIn (V ⊓ offN μ T) (Oinf μ ν a) x, rhoL μ (T.mk' v).1 g f ∈ eigIn (V ⊓ offN μ T) (Oinf μ ν a) x) ∧
          ∀ (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ v, v ∈ nsS T ↔ v ∈ Set.range p) →
          ∀ U : ∀ i, Subgroup (Gw n (T.mk' (p i)).1), (∀ i, CO (U i)) →
            FiniteDimensional ℂ ↥(eigIn (V ⊓ offN μ T) (Oinf μ ν a) x ⊓ ⨅ i, fixL μ (T.mk' (p i)).1 (U i)) := by
  intro F E _ _ _ _ _ σ n hn μ _ ν _ a q w₀ T V hV huniq x hx
  refine ⟨Zv_closed μ T V hV.closed _ x, ?_, ?_⟩
  · intro v hv g f hf
    obtain ⟨m, _, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E n hn).2.1 μ ν
    obtain ⟨h1, h2, h3⟩ := (mem_Zv μ T V _ x f).1 hf
    refine (mem_Zv μ T V _ x _).2 ⟨hV.inv _ _ h1, fun w hw => ?_, ?_⟩
    · refine (mem_eigL' μ _ _ _ _).2 fun y hy => ?_
      have hne : w ≠ (T.mk' v).1 := fun h => hw (by rw [h, under_of_over]; exact hv)
      rw [rhoL_comm μ hne, (mem_eigL' μ _ _ _ _).1 (h2 w hw) y hy, map_smul]
    · have hc : Oinf μ ν a (rhoL μ (T.mk' v).1 g f) = rhoL μ (T.mk' v).1 g (Oinf μ ν a f) :=
        DFunLike.congr_fun ((UpperTheory.ConvolutionTheory.Tf.opAlg E n μ ν m).2.2.2.2.2.2.2.2 a (AdelicGLn.localEmbedding (T.mk' v).1 g)).eq f
      rw [hc, h3, map_smul]
  · intro r p hp hpr U hU
    have hfin : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S}.Finite := by
      have : {w : Pl E | w.under (𝓞 F) ∈ insert q T.S} = ⋃ v ∈ insert q T.S, {w : Pl E | w.under (𝓞 F) = v} := by
        ext w
        simp
      rw [this]
      exact (Finset.finite_toSet _).biUnion fun v _ => finite_over v
    set P : Finset (Pl E) := hfin.toFinset with hP
    have hPm : ∀ w, w ∈ P ↔ w.under (𝓞 F) ∈ insert q T.S := fun w => by simp [hP]
    let f : Fin r → Pl E := fun i => (T.mk' (p i)).1
    have hf : Function.Injective f := fun i j hij => hp (by
      have := congrArg (fun w : Pl E => w.under (𝓞 F)) hij
      simpa only [f, under_of_over] using this)
    obtain ⟨U', hU1, hU2⟩ := exists_ext (B := fun w : Pl E => Subgroup (Gw n w)) f hf U
      (fun w => kerChr (T.J w) (T.χ w) (T.chr w))
    have hU' : ∀ w ∈ P, CO (U' w) := fun w _ => by
      by_cases hw : w ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hw
        rw [hU1]
        exact hU i
      · rw [hU2 w hw]
        exact kerChr_co (T.co w) (T.chr w)
    have hoff : ∀ w : Pl E, w ∉ Set.range f → w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) := fun w hw h => by
      have h' : w.under (𝓞 F) ∈ nsS T := h
      have e := huniq _ h' ⟨w, ⟨rfl⟩⟩
      obtain ⟨i, hi⟩ := (hpr _).1 h'
      refine hw ⟨i, ?_⟩
      have e' : w = (T.mk' (w.under (𝓞 F))).1 := congrArg Subtype.val e
      exact (congrArg (fun v => (T.mk' v).1) hi).trans e'.symm
    haveI := UpperTheory.ConvolutionTheory.C.eigAdm E n hn μ ν a x hx P U' hU'
    refine Submodule.finiteDimensional_of_le (fun v hv => ?_)
      (S₂ := eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ P ⊓ ⨅ w ∈ P, fixL μ w (U' w))
    obtain ⟨hZ, hfx⟩ := Submodule.mem_inf.1 hv
    obtain ⟨h1, h2, h3⟩ := (mem_Zv μ T V _ x v).1 hZ
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hV.le h1, ?_⟩, ?_⟩, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe, h3]
    · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun hw => ?_
      have hu : w.under (𝓞 F) ∉ insert q T.S := fun h => hw ((hPm w).2 h)
      have hS : w.under (𝓞 F) ∉ T.S := fun h => hu (Finset.mem_insert_of_mem h)
      obtain ⟨e1, e2⟩ := T.off w hS (fun h => hu (by rw [h]; exact Finset.mem_insert_self _ _))
      have hns : w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) := fun h => hS (Finset.mem_filter.1 h).1
      refine (mem_fixL' μ _ _ _).2 fun y hy => ?_
      rw [(mem_eigL' μ _ _ _ _).1 (h2 w hns) y (e1 ▸ hy), e2]
      simp
    · refine (Submodule.mem_iInf _).2 fun w => (Submodule.mem_iInf _).2 fun _ => ?_
      by_cases hw : w ∈ Set.range f
      · obtain ⟨i, rfl⟩ := hw
        rw [hU1]
        exact (Submodule.mem_iInf _).1 hfx i
      · rw [hU2 w hw]
        refine (mem_fixL' μ _ _ _).2 fun y hy => ?_
        rw [(mem_eigL' μ _ _ _ _).1 (h2 w (hoff w hw)) y hy.1, hy.2, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IntegralOpEigenlineScalarOfTwist
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.integralOp_eigenline_scalar_of_twist :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
        [m.IsHaarMeasure] (τ : SmIrr G) (I : τ.V ≃ₗ[ℂ] τ.V) (s : G →* G) (J : Subgroup G) (χ : G → ℂ) (A : τ.V →ₗ[ℂ] τ.V) (e : τ.V),
        CO J → IsChr J χ → m J = 1 → IsIntegralOp m τ.ρ ((J : Set G).indicator fun x => conj (χ x)) A →
        e ≠ 0 → (∀ g ∈ J, τ.ρ g e = χ g • e) → (∀ x : τ.V, (∀ g ∈ J, τ.ρ g x = χ g • x) → ∃ c : ℂ, x = c • e) →
        (∀ x ∈ J, s x ∈ J ∧ χ (s x) = χ x) → (∀ g x, I (τ.ρ g x) = τ.ρ (s g) (I x)) →
        ∃ t : ℂ, t ≠ 0 ∧ HasTwTrace m τ I ((J : Set G).indicator fun x => conj (χ x)) t := by
  intro G _ _ _ _ _ m _ τ I s J χ A e hCO hχ hm hA he hty hone hs hI
  have hJo : IsOpen (J : Set G) := hCO.2
  have hcc : ∀ g ∈ J, conj (χ g) * χ g = 1 := by
    intro g hg
    rw [Complex.conj_mul', hχ.2.1 g hg]
    simp

  have hAe : A e = e := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA e l).2]
    have h1 : (fun g => ((J : Set G).indicator (fun x => conj (χ x)) g) * l (τ.ρ g e)) =
        (J : Set G).indicator fun _ => l e := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hty g hg, map_smul, smul_eq_mul,
          ← mul_assoc, hcc g hg, one_mul]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    rw [h1, integral_indicator_const _ hJo.measurableSet]
    simp [Measure.real, hm]

  have hAty : ∀ x, ∀ u ∈ J, τ.ρ u (A x) = χ u • A x := by
    intro x u hu
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 := (hA x (l ∘ₗ τ.ρ u)).2
    have h2 := (hA x l).2
    rw [map_sub, map_smul, sub_eq_zero, h2, smul_eq_mul, ← integral_const_mul,
      ← integral_mul_left_eq_self (fun g => χ u * (((J : Set G).indicator (fun x => conj (χ x)) g) * l (τ.ρ g x))) u]
    refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    have h3 : χ u * (J : Set G).indicator (fun x => conj (χ x)) (u * g) =
        (J : Set G).indicator (fun x => conj (χ x)) g := by
      by_cases hg : g ∈ J
      · have hug : u * g ∈ (J : Set G) := J.mul_mem hu hg
        have hg' : g ∈ (J : Set G) := hg
        rw [Set.indicator_of_mem hug, Set.indicator_of_mem hg', hχ.2.2 u hu g hg, map_mul, ← mul_assoc,
          mul_comm (χ u), hcc u hu, one_mul]
      · have hug : u * g ∉ (J : Set G) := fun h => hg ((J.mul_mem_cancel_left hu).1 h)
        have hg' : g ∉ (J : Set G) := hg
        rw [Set.indicator_of_notMem hug, Set.indicator_of_notMem hg', mul_zero]
    simp only [← mul_assoc, h3, map_mul, LinearMap.comp_apply, Module.End.mul_apply]

  obtain ⟨a, ha⟩ := hone (I.symm e) (by
    intro g hg
    apply I.injective
    rw [hI, map_smul, LinearEquiv.apply_symm_apply, hty _ (hs g hg).1, (hs g hg).2])
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact he (by simpa using ha)
  have hIe : I e = a⁻¹ • e := by
    have h1 : e = a • I e := by
      have := congrArg I ha
      rwa [LinearEquiv.apply_symm_apply, map_smul] at this
    rw [eq_inv_smul_iff₀ ha0]
    exact h1.symm
  obtain ⟨t, ht, htr⟩ := UpperTheory.V.Z.Tf.L4.traceLine τ.V (Submodule.span ℂ {e}) (finrank_span_singleton he) A 1 one_ne_zero
    (fun v => by
      obtain ⟨c, hc⟩ := hone (A v) (hAty v)
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    (fun v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hAe, one_smul])
    I
    (fun v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hIe]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
  exact ⟨t, ht, A, hA, htr⟩
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IsotypicIntersectionProductEq
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_fix' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v : H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, a v = v) → l.prod v = v
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.prod_cons]
    show a (l.prod v) = v
    rw [prod_fix' v l fun b hb => hl b (List.mem_cons_of_mem _ hb), hl a List.mem_cons_self]

theorem UpperTheory.isotypic_intersection_product_eq :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ L : ∀ i, Subgroup (G i), (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i))) → (Z ⊓ ⨅ i, fixU (π i) (L i)) ≠ ⊥ → ∃ κ : ℂ, ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i v, T i v ∈ fixU (π i) (L i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (L i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (L i)) ((List.ofFn T).prod ∘L R) = κ * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI L hL hne
  obtain ⟨K, hK, hKL, hsK⟩ : ∃ K : ∀ i, Subgroup (G i),
      (∀ i, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i))) ∧ (∀ i, K i ≤ L i) ∧
        ∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i := by
    refine ⟨fun i => L i ⊓ (L i).map ((s i).toMulEquiv : G i →* G i), fun i => ⟨?_, ?_⟩, fun i => inf_le_left, ?_⟩
    · have h2 : IsCompact (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (hL i).1.image (s i).continuous
      rw [Subgroup.coe_inf]
      exact (hL i).1.inter h2
    · have h2 : IsOpen (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (s i).toHomeomorph.isOpenMap _ (hL i).2
      rw [Subgroup.coe_inf]
      exact (hL i).2.inter h2
    · rintro i k ⟨-, y, hy, rfl⟩
      show (s i).symm (s i y) ∈ L i
      rw [(s i).symm_apply_apply]
      exact hy
  have hXX : (Z ⊓ ⨅ i, fixU (π i) (L i)) ≤ (Z ⊓ ⨅ i, fixU (π i) (K i)) := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
    exact Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j u hu =>
      (Submodule.mem_iInf _).1 h2 j u (hKL j hu)⟩
  haveI hfdX : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) := hadm K hK
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) := hadm L hL
  have hneX : (Z ⊓ ⨅ i, fixU (π i) (K i)) ≠ ⊥ := fun e => hne (le_bot_iff.1 (e ▸ hXX))
  obtain ⟨h1, c, hcc, hcf, hsp⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV K hK hfdX hneX
  obtain ⟨h1L, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV L hL hfdL hne
  haveI : ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (K i)) := fun i => (h1 i).1
  have hLK : ∀ i, fixedVectors (τ i) (L i) ≤ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => mem_fixedVectors.1 hx k (hKL i hk)
  have hIm : ∀ i, ∀ x ∈ fixedVectors (τ i) (L i), I i x ∈ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => by
      have h := hI i ((s i).symm k) x
      rw [(s i).apply_symm_apply, mem_fixedVectors.1 hx _ (hsK i k hk)] at h
      exact h.symm
  let e : ∀ i, fixedVectors (τ i) (K i) →ₗ[ℂ] S i := fun i =>
    (fixedVectors (τ i) (L i)).subtype ∘ₗ fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 ∘ₗ (fixedVectors (τ i) (K i)).subtype
  let J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (((I i : S i →ₗ[ℂ] S i)) ∘ₗ e i).codRestrict (fixedVectors (τ i) (K i)) fun x =>
      hIm i _ (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x).2
  have he : ∀ i (x : fixedVectors (τ i) (K i)), (x : S i) ∈ fixedVectors (τ i) (L i) → e i x = x := fun i x hx =>
    fixedProj_apply_of_mem (hsm i) (hL i).1 (hL i).2 hx
  have hJ0 : ∀ i, J i ≠ 0 := fun i h0 => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h1L i).2
    have h := LinearMap.congr_fun h0 ⟨x, hLK i hx⟩
    have h' : I i (e i ⟨x, hLK i hx⟩) = 0 := congrArg Subtype.val h
    rw [he i ⟨x, hLK i hx⟩ hx] at h'
    exact hx0 ((I i).map_eq_zero_iff.1 h')
  obtain ⟨ρ, hρ1, hρ2⟩ := UpperTheory.isotypic_submodule_product_decomposition r G H S π τ Z hsm hcm hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J
    (fun i x => rfl) hcf hsp
  obtain ⟨κ, hκ⟩ := UpperTheory.exists_scalar_of_twisted_intertwiner_commuting_algebras r ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) (fun i => fixedVectors (τ i) (K i)) c J ρ hcc hJ0 hρ2
  refine ⟨κ, fun T A t hT1 hT2 hT3 hT4 hA ht => ?_⟩
  let B : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (A i ∘ₗ (fixedVectors (τ i) (K i)).subtype).codRestrict (fixedVectors (τ i) (K i)) fun x => hLK i (hA i _)
  have hcomp := UpperTheory.isotypic_subspace_product_closed r G H S π τ Z K c T B hcf hsp (fun i f hf x => hT4 i f hf x)
  have hPrZ : ∀ v ∈ Z, (List.ofFn fun j => prj (fixU (π j) (L j))).prod v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hcm i j hij)).1 h v)
  have hTZ := UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L T hT1 hT2 hT3
  have hPrFix : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)), (List.ofFn fun j => prj (fixU (π j) (L j))).prod v = v := fun v hv =>
    prod_fix' v _ fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.1 v
        ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hv).2 i)
  let W : H →L[ℂ] H := (List.ofFn T).prod ∘L R ∘L (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have e1 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (K i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).1
    ((List.ofFn fun i => c i (B i)).prod * ρ) fun v => by
      rw [Module.End.mul_apply, hcomp, hρ1]
      rfl
  have hWX : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (K i)), W v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) := fun v hv =>
    hTZ _ (hRZ _ (Submodule.mem_inf.1 (hPrZ v (Submodule.mem_inf.1 hv).1)).1)
  have e2 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).2 hXX hWX
  let b : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    ((W : H →ₗ[ℂ] H) ∘ₗ (Z ⊓ ⨅ i, fixU (π i) (L i)).subtype).codRestrict _ fun v => hWX _ (hXX v.2)
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i)) W).1 b fun v => rfl
  have e4 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i))
    ((List.ofFn T).prod ∘L R)).1 b fun v => by
      show W v = _
      show (List.ofFn T).prod (R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (v : H))) = _
      rw [hPrFix _ v.2]
      rfl
  have ht' : ∀ i, LinearMap.trace ℂ (fixedVectors (τ i) (K i)) (B i * J i) = t i := fun i =>
    UpperTheory.trace_restrict_eq_of_hasFinTrace (S i) (fixedVectors (τ i) (L i)) (fixedVectors (τ i) (K i)) (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)
      (B i * J i) (e i) (hLK i) (ht i) (fun x => hA i _) (fun x => rfl) (he i)
  rw [e4, ← e3, ← e2, e1, hκ B]
  simp only [ht']
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.LeClosureSpanAllOfCommutingUnitaryReps
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_keep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Submodule ℂ H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, ∀ v ∈ Y, a v ∈ Y) → ∀ v, (v ∈ Y ∨ ∃ a ∈ l, ∀ v, a v ∈ Y) → l.prod v ∈ Y
  | [], _, v, h => by simpa using h
  | a :: l, hl, v, h => by
    rw [List.prod_cons]
    show a (l.prod v) ∈ Y
    have ih := prod_keep Y l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) v
    rcases h with h | ⟨b, hb, h⟩
    · exact hl a List.mem_cons_self _ (ih (Or.inl h))
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h _
      · exact hl a List.mem_cons_self _ (ih (Or.inr ⟨b, hb, h⟩))

private theorem prod_fix {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v : H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, a v = v) → l.prod v = v
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.prod_cons]
    show a (l.prod v) = v
    rw [prod_fix v l fun b hb => hl b (List.mem_cons_of_mem _ hb), hl a List.mem_cons_self]

set_option maxHeartbeats 800000 in
theorem UpperTheory.le_closure_spanAll_of_commuting_unitaryReps :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → Z ≠ ⊥ → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i))) ∧ ∃ N : ℕ, 0 < N ∧ ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i (x : fixedVectors (τ i) (U i)), ((B i x : fixedVectors (τ i) (U i)) : S i) = A i x) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) (List.ofFn T).prod = N * ∏ i, LinearMap.trace ℂ (fixedVectors (τ i) (U i)) (B i) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hfd hne
  have lev := UpperTheory.commuting_smooth_irreducible_fixed_vectors r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV
  have hX : ∀ (U : ∀ i, Subgroup (G i)) v, v ∈ Z ⊓ ⨅ i, fixU (π i) (U i) ↔ v ∈ Z ∧ ∀ i, v ∈ fixU (π i) (U i) := fun U v => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  obtain ⟨U₀, hU₀, h0⟩ := UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot r G H π hcm Z hZc hZi hne
  have hmono : ∀ L U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → Z ⊓ ⨅ i, fixU (π i) (U i) ≤ Z ⊓ ⨅ i, fixU (π i) (L i) :=
    fun L U h v hv => (hX L v).2 ⟨hv.1, fun i u hu => ((hX U v).1 hv).2 i u (h i hu)⟩
  have hmS : ∀ i (L U : Subgroup (G i)), L ≤ U → fixedVectors (τ i) U ≤ fixedVectors (τ i) L :=
    fun i L U h v hv => mem_fixedVectors.2 fun u hu => mem_fixedVectors.1 hv u (h hu)
  have hco : ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) →
      ∀ i, IsCompact ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) ∧ IsOpen ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) :=
    fun U hU i => ⟨(hU i).1.inter (hU₀ i).1, (hU i).2.inter (hU₀ i).2⟩
  have hne' : ∀ U : ∀ i, Subgroup (G i), (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ≠ ⊥ := fun U e =>
    h0 (le_bot_iff.1 (e ▸ hmono _ U₀ fun i => inf_le_right))
  have hS : ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) →
      ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) := fun U hU i => by
    have := ((lev _ (hco U hU) (hfd _ (hco U hU)) (hne' U)).1 i).1
    exact Submodule.finiteDimensional_of_le (hmS i (U i ⊓ U₀ i) _ inf_le_left)
  refine ⟨hS, ?_⟩
  have shift : ∀ L : ∀ i, Subgroup (G i), (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i))) →
      (Z ⊓ ⨅ i, fixU (π i) (L i)) ≠ ⊥ → ∃ N : ℕ, ∀ U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i (x : fixedVectors (τ i) (U i)), ((B i x : fixedVectors (τ i) (U i)) : S i) = A i x) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) (List.ofFn T).prod = N * ∏ i, LinearMap.trace ℂ (fixedVectors (τ i) (U i)) (B i) := by
    intro L hL hLne
    obtain ⟨-, N, hN⟩ := lev L hL (hfd L hL) hLne
    refine ⟨N, fun U hLU hU T A B h1 h2 h3 h4 h5 h6 => ?_⟩
    have k1 : ∀ i j (J : Subgroup (G j)), J ≤ U j → ∀ v ∈ fixU (π j) J, T i v ∈ fixU (π j) J := fun i j J hJ v hv u hu => by
      by_cases e : i = j
      · subst e; exact h1 i v u (hJ hu)
      · rw [← h3 i j e, hv u hu]
    have := hfd L hL
    have := hfd U hU
    have := hS L hL
    have := hS U hU
    let p : ∀ i, fixedVectors (τ i) (L i) →ₗ[ℂ] fixedVectors (τ i) (U i) := fun i =>
      (A i ∘ₗ (fixedVectors (τ i) (L i)).subtype).codRestrict _ fun x => h5 i _
    let q : ∀ i, fixedVectors (τ i) (U i) →ₗ[ℂ] fixedVectors (τ i) (L i) := fun i => Submodule.inclusion (hmS i _ _ (hLU i))
    have e1 := hN T (fun i => q i ∘ₗ p i) (fun i v hv => (hX L _).2 ⟨h2 i v hv.1, fun j => k1 i j _ (hLU j) v (((hX L v).1 hv).2 j)⟩)
      fun i f hf x => h4 i f hf x
    have e2 : ∀ i, LinearMap.trace ℂ _ (q i ∘ₗ p i) = LinearMap.trace ℂ _ (B i) := fun i => by
      rw [LinearMap.trace_comp_comm']
      exact congrArg _ (LinearMap.ext fun x => Subtype.ext (h6 i x).symm)
    simp only [e2] at e1
    rw [← e1]
    refine ((UpperTheory.trOn_restrict_and_eq_of_maps_into H _ _ _).2 (hmono L U hLU) fun v hv => (hX U _).2 ⟨?_, fun j => ?_⟩).symm
    · exact prod_keep Z _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact h2 i) v (Or.inl hv.1)
    · exact prod_keep _ _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact k1 i j _ le_rfl) v
        (Or.inr ⟨T j, List.mem_ofFn.2 ⟨j, rfl⟩, h1 j⟩)
  have key : ∀ L : ∀ i, Subgroup (G i), (∀ i, L i ≤ U₀ i) → ∀ N : ℕ, (∀ U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i (x : fixedVectors (τ i) (U i)), ((B i x : fixedVectors (τ i) (U i)) : S i) = A i x) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) (List.ofFn T).prod = N * ∏ i, LinearMap.trace ℂ (fixedVectors (τ i) (U i)) (B i)) →
      Module.finrank ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) = N * ∏ i, Module.finrank ℂ (fixedVectors (τ i) (U₀ i)) := by
    intro L hL N hN
    have := hfd U₀ hU₀
    have := hS U₀ hU₀
    have e1 := hN U₀ hL hU₀ (fun i => prj (fixU (π i) (U₀ i)))
      (fun i => (fixedVectors (τ i) (U₀ i)).subtype ∘ₗ fixedProj (τ i) (hsm i) (hU₀ i).1 (hU₀ i).2) (fun _ => 1)
      (fun i => (UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π i) (U₀ i) (U₀ i)).1)
      (fun i => (UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π i) (U₀ i) (U₀ i)).2.2.1 Z hZc (hZi i))
      (fun i j hij => ((UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π j) (U₀ i) (U₀ j)).2.2.2 (hcm i j hij)).1)
      (fun i f hf x => UpperTheory.fixedProjection_apply_equivariant_eq _ H _ (τ i) (hsm i) (π i) (U₀ i) (hU₀ i).1 (hU₀ i).2 f hf x)
      (fun i x => (fixedProj (τ i) (hsm i) (hU₀ i).1 (hU₀ i).2 x).2)
      (fun i x => (fixedProj_apply_of_mem (hsm i) (hU₀ i).1 (hU₀ i).2 x.2).symm)
    rw [(UpperTheory.trOn_restrict_and_eq_of_maps_into H _ (Z ⊓ ⨅ i, fixU (π i) (U₀ i)) _).1 1 fun v => (prod_fix _ _ fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact (UpperTheory.fixedProjection_invariant_and_commuting_reps _ _ H (π i) (π i) (U₀ i) (U₀ i)).2.1 _ (((hX U₀ _).1 v.2).2 i)).symm] at e1
    simp only [LinearMap.trace_one] at e1
    exact_mod_cast e1
  obtain ⟨N, hN⟩ := shift U₀ hU₀ h0
  have := hfd U₀ hU₀
  have hpos : 0 < Module.finrank ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) :=
    Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 h0)
  have k0 := key U₀ (fun _ => le_rfl) N hN
  rw [k0] at hpos
  refine ⟨N, Nat.pos_of_mul_pos_right hpos, fun U hU => ?_⟩
  obtain ⟨N', hN'⟩ := shift _ (hco U hU) (hne' U)
  obtain rfl : N' = N := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_mul_pos_left hpos)
    ((key _ (fun _ => inf_le_right) N' hN').symm.trans k0)
  exact hN' U (fun _ => inf_le_left) hU
end

