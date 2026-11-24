module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ProdLocalOperatorsMemFixedAndOffNCMDatum
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  simp only [rhoL, map_mul, this]

private theorem rhoL_comm {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') :
    Commute (rhoL μ w g) (rhoL μ w' g') := by
  have h1 := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  show rhoL μ w g ∘L rhoL μ w' g' = rhoL μ w' g' ∘L rhoL μ w g
  simp only [rhoL, ← h1, h2]

private theorem oloc_comm {w : Pl K} [MeasurableSpace (Gw n w)] {m : Measure (Gw n w)} {ψ : Gw n w → ℂ}
    {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (R : LL μ →L[ℂ] LL μ) (hR : ∀ g, Commute R (rhoL μ w g)) :
    Commute R Bo := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  show ⟪u, R (Bo v)⟫_ℂ = ⟪u, Bo (R v)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left R, h, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ g * _
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR g).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [this]

private theorem oloc_fix {w : Pl K} [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] {m : Measure (Gw n w)}
    [m.IsHaarMeasure] {ψ : Gw n w → ℂ} {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (J : Subgroup (Gw n w))
    (hJ : ∀ u ∈ J, ∀ g, ψ (u * g) = ψ g) (v : LL μ) : Bo v ∈ fixL μ w J := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  refine ext_inner_left ℂ fun a => ?_
  show ⟪a, rhoL μ w u (Bo v)⟫_ℂ = ⟪a, Bo v⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left (rhoL μ w u), h, h,
    ← integral_mul_left_eq_self (μ := m) (fun g => ψ g * ⟪a, rhoL μ w g v⟫_ℂ) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ (u * g) * _
  rw [hJ u hu, rhoL_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

private theorem mem_eigL {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {v : LL μ} :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem mem_fixL {w : Pl K} {J : Subgroup (Gw n w)} {v : LL μ} :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).trans ⟨fun h x hx => h _ ⟨x, hx, rfl⟩, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  exact h x hx

end Ops

private theorem prod_range {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Set H) (l : List (H →L[ℂ] H))
    (hl : ∀ O ∈ l, ∀ v ∈ X, O v ∈ X) (hO : ∃ O ∈ l, ∀ v, O v ∈ X) (f : H) : l.prod f ∈ X := by
  induction l with
  | nil => obtain ⟨O, hO, -⟩ := hO; simp at hO
  | cons a t ih =>
    rw [List.prod_cons, ContinuousLinearMap.mul_apply]
    obtain ⟨O, hO, hr⟩ := hO
    rcases List.mem_cons.1 hO with rfl | ht
    · exact hr _
    · exact hl a List.mem_cons_self _ (ih (fun O' h' => hl O' (List.mem_cons_of_mem _ h')) ⟨O, ht, hr⟩)

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.prod_localOperators_mem_fixed_and_offN_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q)
        (T : Ty σ n q w₀) (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ i, p i ∈ nsS T) →
        ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (mm : ∀ u : Pl E, Measure (Gw n u)),
          (∀ u, (mm u).IsHaarMeasure) →
        ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) (U : ∀ i, Subgroup (Gw n (T.mk' (p i)).1)),
          (∀ i, ∀ u ∈ U i, ∀ g, ψ (p i) (u * g) = ψ (p i) g) →
        ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
          (∀ f, (List.ofFn B).prod f ∈ ⨅ i, fixL μ (T.mk' (p i)).1 (U i)) ∧ (∀ f ∈ offN μ T, (List.ofFn B).prod f ∈ offN μ T) := by
  intro F E _ _ _ _ _ σ n μ _ q w₀ T r p hp hns _ _ mm hmm ψ U hU B hB
  have hfix : ∀ i v, B i v ∈ fixL μ (T.mk' (p i)).1 (U i) := fun i v => by
    haveI := hmm (T.mk' (p i)).1
    exact oloc_fix μ (hB i) (U i) (hU i) v
  have hne : ∀ i j, i ≠ j → (T.mk' (p i)).1 ≠ (T.mk' (p j)).1 := fun i j hij h =>
    hij (hp ((under_eq (T.mk' (p i))).symm.trans
      ((congrArg (fun w : Pl E => w.under (𝓞 F)) h).trans (under_eq (T.mk' (p j))))))
  have hcomm : ∀ i (w : Pl E), w ≠ (T.mk' (p i)).1 → ∀ (g : Gw n w) (v : LL μ),
      B i (rhoL μ w g v) = rhoL μ w g (B i v) := fun i w hw g v => by
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v)
      (oloc_comm μ (hB i) (rhoL μ w g) fun g' => rhoL_comm μ hw g g').eq
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this.symm
  refine ⟨fun f => ?_, ?_⟩
  · rw [Submodule.mem_iInf]
    intro i
    refine prod_range (fixL μ (T.mk' (p i)).1 (U i) : Set (LL μ)) (List.ofFn B) (fun O hO v hv => ?_)
      ⟨B i, (List.mem_ofFn' _ _).2 ⟨i, rfl⟩, hfix i⟩ f
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    by_cases h : j = i
    · subst h
      exact hfix j v
    · refine (mem_fixL μ).2 fun x hx => ?_
      rw [← hcomm j _ (hne i j (Ne.symm h)) x v, (mem_fixL μ).1 hv x hx]
  · have hoff : ∀ {v : LL μ}, v ∈ offN μ T ↔
        ∀ w : Pl E, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
      intro v
      simp only [offN, Submodule.mem_iInf, mem_eigL]
    have key : ∀ O ∈ List.ofFn B, ∀ f ∈ offN μ T, O f ∈ offN μ T := by
      intro O hO f hf
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
      refine hoff.2 fun w hw x hx => ?_
      have hwi : w ≠ (T.mk' (p i)).1 := fun h => hw (by
        rw [h, under_eq]
        exact hns i)
      rw [← hcomm i w hwi x f, hoff.1 hf w hw x hx, map_smul]
    exact List.prod_induction (fun O : LL μ →L[ℂ] LL μ => ∀ f ∈ offN μ T, O f ∈ offN μ T)
      (fun a b ha hb f hf => ha _ (hb f hf)) (fun f hf => hf) key
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TraceEigenspaceOfSelfAdjointInvariantSubspaces
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.RedH

section Hil
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_mem_cl {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : v ∈ V.topologicalClosure ↔ v ∈ V := by
  rw [hV.submodule_topologicalClosure_eq]

private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V :=
  (prj_mem_cl hV _).1 (Submodule.starProjection_apply_mem _ v)

private theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem prj_adj (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V :=
  (isSelfAdjoint_starProjection _).adjoint_eq

private theorem prj_comm {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H)
    (hT : ContinuousLinearMap.adjoint T = T) (h : ∀ v ∈ V, T v ∈ V) : T * prj V = prj V * T := by
  refine ContinuousLinearMap.ext fun v => ?_
  show T (prj V v) = prj V (T v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((prj_mem_cl hV _).2 (h _ (prj_mem hV v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, hT]
  exact Submodule.starProjection_inner_eq_zero v _ ((prj_mem_cl hV _).2 (h w ((prj_mem_cl hV _).1 hw)))

private theorem eigIn_closed {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (A : H →L[ℂ] H) (x : ℝ) :
    IsClosed (eigIn W A x : Set H) := by
  have : (eigIn W A x : Set H) = (W : Set H) ∩ {v | A v = (x : ℂ) • v} := by
    ext v
    simp [eigIn, Module.End.mem_eigenspace_iff]
  rw [this]
  exact hW.inter (isClosed_eq A.continuous (continuous_const_smul _))

private theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Module.End.mem_eigenspace_iff]

private theorem prj_inf {P X : Submodule ℂ H} (hP : IsClosed (P : Set H)) (hX : IsClosed (X : Set H))
    (h : ∀ v ∈ X, prj P v ∈ X) : prj X * prj P = prj (X ⊓ P) ∧ prj P * prj X = prj (X ⊓ P) := by
  have hc := prj_comm hX (prj P) (prj_adj P) h
  have hXP : IsClosed ((X ⊓ P : Submodule ℂ H) : Set H) := by
    rw [Submodule.coe_inf]; exact hX.inter hP
  have key : prj X * prj P = prj (X ⊓ P) := by
    refine ContinuousLinearMap.ext fun v => ?_
    show prj X (prj P v) = (X ⊓ P).topologicalClosure.starProjection v
    symm
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · refine (prj_mem_cl hXP _).2 ⟨prj_mem hX _, ?_⟩
      have := congrArg (fun S : H →L[ℂ] H => S v) hc
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [← this]
      exact prj_mem hP _
    · have hw' := (prj_mem_cl hXP _).1 hw
      have hs : ∀ (Q : Submodule ℂ H) (a b : H), ⟪prj Q a, b⟫_ℂ = ⟪a, prj Q b⟫_ℂ := fun Q a b => by
        rw [← ContinuousLinearMap.adjoint_inner_right, prj_adj]
      rw [inner_sub_left, hs, hs, prj_self hw'.1, prj_self hw'.2, sub_self]
  exact ⟨key, hc.trans key⟩

private theorem core (Ty Fx V : Submodule ℂ H) (hTy : IsClosed (Ty : Set H)) (hFx : IsClosed (Fx : Set H))
    (hV : IsClosed (V : Set H)) (hle : Ty ≤ Fx) (Oa : H →L[ℂ] H) (hOa : ContinuousLinearMap.adjoint Oa = Oa)
    (hOT : ∀ v ∈ Ty, Oa v ∈ Ty) (hOF : ∀ v ∈ Fx, Oa v ∈ Fx) (hVT : ∀ v ∈ Ty, prj V v ∈ Ty) (x : ℝ) :
    prj (eigIn V (Oa ∘L prj Fx) x) * prj Ty = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj Ty * prj (eigIn V (Oa ∘L prj Fx) x) = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj (eigIn V (Oa ∘L prj Fx) x) * (Oa ∘L prj Fx) = (x : ℂ) • prj (eigIn V (Oa ∘L prj Fx) x) := by
  set A := Oa ∘L prj Fx with hA
  set X := eigIn V A x with hXd
  have hXc : IsClosed (X : Set H) := eigIn_closed hV A x
  have hOP : Oa * prj Ty = prj Ty * Oa := prj_comm hTy Oa hOa hOT
  have hOFx : Oa * prj Fx = prj Fx * Oa := prj_comm hFx Oa hOa hOF
  have hVP : prj V * prj Ty = prj Ty * prj V := prj_comm hTy (prj V) (prj_adj V) hVT
  have hFP : prj Fx * prj Ty = prj Ty := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact prj_self (hle (prj_mem hTy v))
  have hPF : prj Ty * prj Fx = prj Ty :=
    (prj_comm hFx (prj Ty) (prj_adj Ty) fun v _ => hle (prj_mem hTy v)).trans hFP
  have hAP : A * prj Ty = prj Ty * A := by
    show Oa * prj Fx * prj Ty = prj Ty * (Oa * prj Fx)
    rw [mul_assoc, hFP, hOP, ← mul_assoc, ← hOP, mul_assoc, hPF, hOP]
  have hAadj : star A = A := by
    show star (Oa * prj Fx) = Oa * prj Fx
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, hOa, prj_adj, hOFx]
  have heq : X ⊓ Ty = eigIn (V ⊓ Ty) Oa x := by
    ext v
    simp only [Submodule.mem_inf, mem_eigIn, hXd]
    have hA1 : v ∈ Ty → A v = Oa v := fun hv => by
      show Oa (prj Fx v) = Oa v
      rw [prj_self (hle hv)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, by rwa [← hA1 h3]⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, by rwa [hA1 h3]⟩, h3⟩
  have hPX : ∀ v ∈ X, prj Ty v ∈ X := by
    intro v hv
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
    refine mem_eigIn.2 ⟨?_, ?_⟩
    · have := congrArg (fun S : H →L[ℂ] H => S v) hVP
      simp only [ContinuousLinearMap.mul_apply, prj_self h1] at this
      rw [← this]
      exact prj_mem hV _
    · have := congrArg (fun S : H →L[ℂ] H => S v) hAP
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [this, h2, map_smul]
  obtain ⟨k1, k2⟩ := prj_inf hTy hXc hPX
  rw [heq] at k1 k2
  refine ⟨k1, k2, ?_⟩
  have hAX : A * prj X = (x : ℂ) • prj X := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact (mem_eigIn.1 (prj_mem hXc v)).2
  have hsX : star (prj X) = prj X := by
    rw [ContinuousLinearMap.star_eq_adjoint, prj_adj]
  have := congrArg star hAX
  rwa [star_mul, star_smul, hAadj, hsX, RCLike.star_def, Complex.conj_ofReal] at this

private theorem isHS_prj (E : Submodule ℂ H) [FiniteDimensional ℂ E] : IsHilbertSchmidt (prj E) := by
  have hcl : E.topologicalClosure = E :=
    (Submodule.closed_of_finiteDimensional E).submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance
  have h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL) := by
    rw [isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top enorm_lt_top
  exact h1.comp_right E.topologicalClosure.orthogonalProjection

private theorem prj_idem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) : prj V * prj V = prj V :=
  ContinuousLinearMap.ext fun v => prj_self (prj_mem hV v)

private theorem trace_sm (c : ℂ) (S : H →L[ℂ] H) : trace (c • S) = c * trace S := by
  simp only [trace, ContinuousLinearMap.smul_apply, inner_smul_right, tsum_mul_left]

private theorem alg {R : Type} [Ring R] [Algebra ℂ R] (PX P PY A Oa U S Θ : R) (k x : ℂ)
    (h1 : PX * P = PY) (h3 : PX * A = x • PX) (h4 : U * A = A * U)
    (h5 : Oa * S = A * S) (h6 : P * (U * S) = U * S) :
    PX * ((U * ((k • (Oa * S)) * Θ)) * PX) = (k * x) • (PY * (((U * S) * Θ) * PX)) := by
  have e1 : U * ((k • (Oa * S)) * Θ) = k • (A * ((U * S) * Θ)) := by
    rw [h5, smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [← mul_assoc]
    rw [h4]
  have e2 : PX * ((U * S) * Θ) = PY * ((U * S) * Θ) := by
    rw [← h1, mul_assoc PX P, ← mul_assoc P, h6]
  rw [e1, smul_mul_assoc, mul_smul_comm, ← mul_assoc PX (A * _), ← mul_assoc PX A, h3, smul_mul_assoc,
    smul_mul_assoc, smul_smul, e2, mul_assoc PY]

end Hil

end UpperTheory.RedH

theorem UpperTheory.trace_eigenspace_of_selfAdjoint_invariant_subspaces :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Ty Fx V : Submodule ℂ H),
        IsClosed (Ty : Set H) → IsClosed (Fx : Set H) → IsClosed (V : Set H) → Ty ≤ Fx → ∀ Oa : H →L[ℂ] H,
        ContinuousLinearMap.adjoint Oa = Oa → (∀ v ∈ Ty, Oa v ∈ Ty) → (∀ v ∈ Fx, Oa v ∈ Fx) → (∀ v ∈ Ty, prj V v ∈ Ty) →
        ∀ (x : ℝ) (κ : ℂ) (U S Θ : H →L[ℂ] H), FiniteDimensional ℂ ↥(eigIn (V ⊓ Ty) Oa x) →
          Commute U (Oa ∘L prj Fx) → (∀ v, S v ∈ Ty) → (∀ v, U (S v) ∈ Ty) →
          trOn (eigIn V (Oa ∘L prj Fx) x) (U ∘L (κ • (Oa ∘L S)) ∘L Θ) = (κ * x) * trOn (eigIn (V ⊓ Ty) Oa x) (U ∘L S ∘L Θ) := by
  intro H _ _ _ Ty Fx V hTy hFx hV hle Oa hOa hOT hOF hVT x κ U S Θ hfin hUA hS hUS
  obtain ⟨k1, k2, k3⟩ := UpperTheory.RedH.core Ty Fx V hTy hFx hV hle Oa hOa hOT hOF hVT x
  set PX := prj (eigIn V (Oa ∘L prj Fx) x) with hPX
  set PY := prj (eigIn (V ⊓ Ty) Oa x) with hPY
  have hXc : IsClosed ((eigIn V (Oa ∘L prj Fx) x : Submodule ℂ H) : Set H) := UpperTheory.RedH.eigIn_closed hV _ x
  have hXX : PX * PX = PX := UpperTheory.RedH.prj_idem hXc
  have hXY : PX * PY = PY := by rw [← k1, ← mul_assoc, hXX]
  have hYc : IsClosed ((eigIn (V ⊓ Ty) Oa x : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hYY : PY * PY = PY := UpperTheory.RedH.prj_idem hYc
  have hHS : IsHilbertSchmidt PY := UpperTheory.RedH.isHS_prj _
  have hTC : IsTraceClass PY := by
    have h := isTraceClass_comp hHS hHS
    have e : PY ∘L PY = PY := hYY
    rwa [e] at h
  have hal := UpperTheory.RedH.alg PX (prj Ty) PY (Oa ∘L prj Fx) Oa U S Θ κ (x : ℂ) k1 k3 hUA.eq
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      show Oa (S v) = Oa (prj Fx (S v))
      rw [UpperTheory.RedH.prj_self (hle (hS v))])
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      exact UpperTheory.RedH.prj_self (hUS v))
  set D : H →L[ℂ] H := (U * S) * Θ with hD
  have t1 : trace (PY * (D * PX)) = trace (D * PY) := by
    have h := trace_comp_comm hTC (D * PX)
    have e1 : (D * PX) ∘L PY = D * PY := by
      show (D * PX) * PY = D * PY
      rw [mul_assoc, hXY]
    rw [e1] at h
    exact h.symm
  have t2 : trace (PY * (D * PY)) = trace (D * PY) := by
    have h := trace_comp_comm hTC (D * PY)
    have e1 : (D * PY) ∘L PY = D * PY := by
      show (D * PY) * PY = D * PY
      rw [mul_assoc, hYY]
    rw [e1] at h
    exact h.symm
  unfold trOn
  rw [← hPX, ← hPY]
  have g1 : PX ∘L (U ∘L (κ • (Oa ∘L S)) ∘L Θ) ∘L PX = (κ * x) • (PY * (D * PX)) := hal
  have g2 : PY ∘L (U ∘L S ∘L Θ) ∘L PY = PY * (D * PY) := by
    show PY * ((U * (S * Θ)) * PY) = PY * (D * PY)
    simp only [hD, mul_assoc]
  rw [g1, g2, UpperTheory.RedH.trace_sm, t1, t2]
end

