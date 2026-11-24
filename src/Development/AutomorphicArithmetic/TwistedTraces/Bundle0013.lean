module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.HeckeOperatorSummandWeightCMDatum
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.EigenLatticeOffDiagonal

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  simp only [rhoL, map_mul, this]

private theorem rhoL_comm {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') : Commute (rhoL μ w g) (rhoL μ w' g') := by
  have h1 := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  show rhoL μ w g ∘L rhoL μ w' g' = rhoL μ w' g' ∘L rhoL μ w g
  simp only [rhoL, ← h1, h2]

private theorem arch_comm (a : archGroup K n) (w : Pl K) (g : Gw n w) :
    Commute (rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a)) (rhoL μ w g) := by
  show rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a) * rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) =
    rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) * rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a)
  rw [← UnitaryRep.map_mul, ← UnitaryRep.map_mul, archimedeanProjection_apply, MultiplicityOne.finProj_mul_archProj_comm]

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

private theorem oloc_fix {w : Pl K} [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] {m : Measure (Gw n w)} [m.IsHaarMeasure]
    {ψ : Gw n w → ℂ} {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (J : Subgroup (Gw n w))
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

private theorem comm_prj {V : Submodule ℂ (LL μ)} (hV : IsClosed (V : Set (LL μ))) (R : LL μ →L[ℂ] LL μ)
    (hR : Commute (prj V) R) (v : LL μ) (hv : v ∈ V) : R v ∈ V := by
  have hself : ∀ x ∈ V, prj V x = x := fun x hx =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hx)
  have h := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) hR.eq
  simp only [ContinuousLinearMap.mul_apply, hself v hv] at h
  rw [← h]
  exact hV.submodule_topologicalClosure_eq.le (Submodule.starProjection_apply_mem V.topologicalClosure (R v))

end Ops

section Ty
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q} (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]

private theorem mem_offN (T : Ty σ n q w₀) {v : LL μ} :
    v ∈ offN μ T ↔ ∀ w, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
  simp only [offN, Submodule.mem_iInf, mem_eigL]

private theorem off_step (T : Ty σ n q w₀) (Bo : LL μ →L[ℂ] LL μ) (w₁ : Pl E)
    (hfix : ∀ v, Bo v ∈ fixL μ w₁ (T.J w₁)) (hχ : T.χ w₁ = 1)
    (hc : ∀ w, w ≠ w₁ → ∀ g, Commute Bo (rhoL μ w g)) (v : LL μ) (hv : v ∈ offN μ T) : Bo v ∈ offN μ T := by
  rw [mem_offN] at hv ⊢
  intro w hw x hx
  by_cases h : w = w₁
  · subst h
    have hch : IsChr (T.J w) 1 := hχ ▸ T.chr w
    have h1 := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) hch).2.1
    have h2 : Bo v ∈ eigL μ w (T.J w) 1 := by rw [h1]; exact hfix v
    rw [hχ]
    exact (mem_eigL μ).1 h2 x hx
  · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hc w h x).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [← this, hv w hw x hx, map_smul]

end Ty

end UpperTheory.EigenLatticeOffDiagonal

open UpperTheory.EigenLatticeOffDiagonal in
theorem UpperTheory.heckeOperator_summand_weight_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q),
        GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ (e : Fin n → ℤ) (j r : ℕ) (p : Fin r → Pl F),
        (∀ i, p i ∈ T.sp) → ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)]
          (mm : ∀ u : Pl E, Measure (Gw n u)), (∀ u, (mm u).IsHaarMeasure ∧ mm u (T.J u) = 1) →
        ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), (∀ i, Test (ψ (p i)) ∧ ∀ u ∈ T.J (T.mk' (p i)).1, ∀ g, ψ (p i) (u * g) = ψ (p i) g) →
        ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
          (∀ g, Commute ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n g))) ∧
          (∀ w ∉ T.marked, ∀ g, Commute ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) (rhoL μ w g)) ∧
          (∀ f ∈ offN μ T, ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) f ∈ offN μ T) ∧
          (∀ f ∈ V, ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) f ∈ V) := by
  intro F E _ _ _ _ _ σ n μ _ q w₀ hq T V hV e j r p hp _ _ mm hmm ψ hψ B hBo
  have hVc : IsClosed (V : Set (LL μ)) := IsSummandOf.closed hV
  have hVrho : ∀ (w : Pl E) (g : Gw n w), Commute (prj V) (rhoL μ w g) := fun w g =>
    ((UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.1 _ V hVc (IsSummandOf.inv hV)).symm
  let Good : (LL μ →L[ℂ] LL μ) → Prop := fun O => (∀ v ∈ offN μ T, O v ∈ offN μ T) ∧
    (∀ g, Commute O (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n g))) ∧
    (∀ w ∉ T.marked, ∀ g, Commute O (rhoL μ w g)) ∧ (∀ v ∈ V, O v ∈ V)
  have hGone : Good 1 := ⟨fun v hv => hv, fun g => Commute.one_left _, fun w _ g => Commute.one_left _, fun v hv => hv⟩
  have hGmul : ∀ O₁ O₂, Good O₁ → Good O₂ → Good (O₁ * O₂) := fun O₁ O₂ h₁ h₂ =>
    ⟨fun v hv => h₁.1 _ (h₂.1 v hv), fun g => (h₁.2.1 g).mul_left (h₂.2.1 g),
      fun w hw g => (h₁.2.2.1 w hw g).mul_left (h₂.2.2.1 w hw g), fun v hv => h₁.2.2.2 _ (h₂.2.2.2 v hv)⟩
  have hBG : Good (List.ofFn B).prod := by
    refine List.prod_induction _ hGmul hGone fun O hO => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    haveI := (hmm (T.mk' (p i)).1).1
    have hsp : p i ∈ T.sp := hp i
    have hspl : GM.Split E (p i) := (Finset.mem_filter.1 hsp).2
    have ht := (hψ i).2
    have hne : ∀ w ∉ T.marked, w ≠ (T.mk' (p i)).1 := fun w hw h => hw (Or.inr ⟨p i, hsp, h⟩)
    refine ⟨off_step μ T (B i) _ (oloc_fix μ (hBo i) _ ht) (T.triv _ hspl _) (fun w hw g => ?_),
      fun g => ?_, fun w hw g => ?_, comm_prj μ hVc _ (oloc_comm μ (hBo i) _ fun g' => hVrho _ g')⟩
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ hw g g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => arch_comm μ g _ g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUG : Good (Uiw μ w₀.1 e) := by
    have hI : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
    have hco := T.co w₀.1
    rw [hI] at hco
    have hh := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w₀.1 (GLnLocal.iwahori _ n) (Cartan.diagPow _ n e) hco.2 hco.1
    have hne : ∀ w ∉ T.marked, w ≠ w₀.1 := fun w hw h => hw (Or.inl h)
    refine ⟨off_step μ T _ w₀.1 (fun v => ?_) (T.triv q hq w₀) (fun w hw g => ?_), fun g => ?_, fun w hw g => ?_,
      comm_prj μ hVc _ (hh.2.2.2.2.1 _ fun g' => hVrho _ g')⟩
    · rw [hI]; exact hh.2.1 v
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ hw g g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => arch_comm μ g _ g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUjG : Good (Uiw μ w₀.1 e ^ j) := by
    induction j with
    | zero => simpa using hGone
    | succ k ih => rw [pow_succ]; exact hGmul _ _ ih hUG
  have hCG : Good ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) := hGmul _ _ hUjG hBG
  exact ⟨hCG.2.1, hCG.2.2.1, hCG.1, hCG.2.2.2⟩
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TrOnProdEigenProjectionsEqTrOnJointEigenspace
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma prj_mem' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (x : H) : prj M x ∈ M := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  have h2 : prj M x ∈ M.topologicalClosure := Submodule.starProjection_apply_mem M.topologicalClosure x
  rwa [h] at h2

private lemma prj_orth' (M : Submodule ℂ H) (x : H) {y : H} (hy : y ∈ M) :
    ⟪x - prj M x, y⟫_ℂ = 0 :=
  (Submodule.mem_orthogonal' _ _).1
    (Submodule.sub_starProjection_mem_orthogonal (K := M.topologicalClosure) x) y
    (M.le_topologicalClosure hy)

private lemma prj_eq' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {u v : H} (hv : v ∈ M)
    (ho : ∀ y ∈ M, ⟪u - v, y⟫_ℂ = 0) : prj M u = v := by
  have h : M.topologicalClosure = M := hM.submodule_topologicalClosure_eq
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := M.topologicalClosure)
    (M.le_topologicalClosure hv) fun y hy => ho y (by rwa [h] at hy)

private lemma prj_self' {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) {v : H} (hv : v ∈ M) :
    prj M v = v :=
  prj_eq' hM hv fun y _ => by simp

private lemma comm_of_stable {M : Submodule ℂ H} (hM : IsClosed (M : Set H)) (B B' : H →L[ℂ] H)
    (hadj : ∀ x y, ⟪B x, y⟫_ℂ = ⟪x, B' y⟫_ℂ) (h1 : ∀ v ∈ M, B v ∈ M) (h2 : ∀ v ∈ M, B' v ∈ M) :
    Commute B (prj M) := by
  refine ContinuousLinearMap.ext fun x => ?_
  show B (prj M x) = prj M (B x)
  refine (prj_eq' hM (h1 _ (prj_mem' hM x)) fun y hy => ?_).symm
  rw [← map_sub, hadj]
  exact prj_orth' M x (h2 y hy)

private lemma hs_prj (W : Submodule ℂ H) [FiniteDimensional ℂ W] : IsHilbertSchmidt (prj W) := by
  have hcl := Submodule.closed_of_finiteDimensional W
  let e := stdOrthonormalBasis ℂ W
  have he : Orthonormal ℂ (fun k => ((e k : W) : H)) :=
    e.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  obtain ⟨s, b, hvs, hb⟩ := (he.toSubtypeRange).exists_hilbertBasis_extension
  have hbi : ∀ i, b i = (i : H) := fun i => congrFun hb i
  let f : Fin _ → s := fun k => ⟨(e k : H), hvs (Set.mem_range_self k)⟩
  have hf : Function.Injective f := fun k l h => by
    have : ((e k : W) : H) = (e l : W) := congrArg (fun z : s => (z : H)) h
    exact he.linearIndependent.injective this
  have hbf : ∀ k, b (f k) = (e k : H) := fun k => hbi _
  have hout : ∀ i, i ∉ Set.range f → prj W (b i) = 0 := fun i hi => by
    refine prj_eq' hcl W.zero_mem fun y hy => ?_
    have hy' : (y : H) = ∑ k, ⟪(e k : H), y⟫_ℂ • (e k : H) := by
      have h2 := congrArg Subtype.val (e.sum_repr' (⟨y, hy⟩ : W))
      simpa [Submodule.coe_sum] using h2.symm
    rw [sub_zero, hy', inner_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [inner_smul_right, ← hbf k]
    have : ⟪b i, b (f k)⟫_ℂ = 0 := b.orthonormal.2 fun h => hi ⟨k, h.symm⟩
    rw [this, mul_zero]
  rw [isHilbertSchmidt_iff b]
  have hs : Function.support (fun i => ‖prj W (b i)‖ₑ ^ 2) ⊆ Set.range f := fun i hi => by
    by_contra h
    exact hi (by simp [hout i h])
  rw [← hf.tsum_eq hs, tsum_fintype]
  exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.pow_lt_top enorm_lt_top

private lemma pr_props (Z : Submodule ℂ H) : ∀ (r : ℕ) (E : Fin r → Submodule ℂ H),
    (∀ i, IsClosed (E i : Set H)) → (∀ i j, Commute (prj (E i)) (prj (E j))) →
    (∀ i, ∀ v ∈ Z, prj (E i) v ∈ Z) →
    (∀ u ∈ Z, (List.ofFn fun i => prj (E i)).prod u ∈ Z) ∧
    (∀ u, (List.ofFn fun i => prj (E i)).prod u ∈ ⨅ i, E i) ∧
    ∀ u, ∀ y ∈ ⨅ i, E i, ⟪u - (List.ofFn fun i => prj (E i)).prod u, y⟫_ℂ = 0 := by
  intro r
  induction r with
  | zero =>
    intro E _ _ _
    simp
  | succ r ih =>
    intro E hE hc hs
    obtain ⟨i1, i2, i3⟩ := ih (fun i => E i.succ) (fun i => hE _) (fun i j => hc _ _) (fun i => hs _)
    have hP : ∀ u, (List.ofFn fun i => prj (E i)).prod u =
        prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) := fun u => by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    refine ⟨fun u hu => ?_, fun u => ?_, fun u y hy => ?_⟩
    · rw [hP]
      exact hs 0 _ (i1 u hu)
    · rw [hP, Submodule.mem_iInf]
      refine Fin.cases (prj_mem' (hE 0) _) fun j => ?_
      have hx := Submodule.mem_iInf _ |>.1 (i2 u) j
      have h1 : prj (E j.succ) (prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) =
          prj (E 0) (prj (E j.succ) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) :=
        congrArg (fun T : H →L[ℂ] H => T ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) (hc j.succ 0).eq
      rw [prj_self' (hE _) hx] at h1
      rw [← h1]
      exact prj_mem' (hE _) _
    · rw [hP]
      have hy0 : y ∈ E 0 := (Submodule.mem_iInf _).1 hy 0
      have hys : y ∈ ⨅ i : Fin r, E i.succ := (Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).1 hy j.succ
      have e : u - prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u) =
          (u - (List.ofFn fun i : Fin r => prj (E i.succ)).prod u) +
          ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u -
            prj (E 0) ((List.ofFn fun i : Fin r => prj (E i.succ)).prod u)) := by abel
      rw [e, inner_add_left, i3 u y hys, prj_orth' _ _ hy0, add_zero]

private lemma tr_main {Z X Y : Submodule ℂ H} (Pr R : H →L[ℂ] H) [FiniteDimensional ℂ X] (hYX : Y ≤ X)
    (hXZ : X ≤ Z) (hR : ∀ v ∈ Z, R v ∈ Z) (h1 : ∀ u ∈ Z, Pr u ∈ Y)
    (h2 : ∀ u, ∀ y ∈ Y, ⟪u - Pr u, y⟫_ℂ = 0) : trOn X (Pr ∘L R) = trOn Y R := by
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYX
  have hXc := Submodule.closed_of_finiteDimensional X
  have hYc := Submodule.closed_of_finiteDimensional Y
  have e1 : prj X ∘L (Pr ∘L R) ∘L prj X = prj Y ∘L (R ∘L prj X) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have hx : R (prj X v) ∈ Z := hR _ (hXZ (prj_mem' hXc v))
    show prj X (Pr (R (prj X v))) = prj Y (R (prj X v))
    rw [prj_self' hXc (hYX (h1 _ hx)), prj_eq' hYc (h1 _ hx) (h2 _)]
  have e2 : (R ∘L prj X) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj X (prj Y v)) = R (prj Y v)
    rw [prj_self' hXc (hYX (prj_mem' hYc v))]
  have e3 : (R ∘L prj Y) ∘L prj Y = R ∘L prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    show R (prj Y (prj Y v)) = R (prj Y v)
    rw [prj_self' hYc (prj_mem' hYc v)]
  have e4 : prj Y ∘L prj Y = prj Y := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact prj_self' hYc (prj_mem' hYc v)
  have hT : IsTraceClass (prj Y) := by
    have := isTraceClass_comp (hs_prj Y) (hs_prj Y)
    rwa [show (prj Y).comp (prj Y) = prj Y from e4] at this
  unfold trOn
  rw [e1]
  have a := trace_comp_comm hT (R ∘L prj X)
  have b := trace_comp_comm hT (R ∘L prj Y)
  calc trace (prj Y ∘L R ∘L prj X) = trace ((R ∘L prj X) ∘L prj Y) := a.symm
    _ = trace ((R ∘L prj Y) ∘L prj Y) := by rw [e2, e3]
    _ = trace (prj Y ∘L R ∘L prj Y) := b

end Hilbert

theorem UpperTheory.trOn_prod_eigenProjections_eq_trOn_joint_eigenspace :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (Z : Submodule ℂ (LL μ))
        (r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (J : ∀ i, Subgroup (Gw n (w i))) (χ : ∀ i, Gw n (w i) → ℂ)
        (hc : ∀ i, IsChr (J i) (χ i)) (R : LL μ →L[ℂ] LL μ), (∀ i, CO (J i)) → IsClosed (Z : Set (LL μ)) →
        (∀ i g, ∀ v ∈ Z, rhoL μ (w i) g v ∈ Z) → (∀ v ∈ Z, R v ∈ Z) →
        FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) →
        trOn (Z ⊓ ⨅ i, fixL μ (w i) (kerChr (J i) (χ i) (hc i))) ((List.ofFn fun i => prj (eigL μ (w i) (J i) (χ i))).prod ∘L R) =
          trOn (Z ⊓ ⨅ i, eigL μ (w i) (J i) (χ i)) R := by
  intro K _ _ n μ _ Z r w hw J χ hc R hCO hZ hst hR hfd
  have hB := fun i => UpperTheory.ConvolutionTheory.L1.eigBasic K n μ (w i) (J i) (χ i) (hCO i) (hc i)
  have hF := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hmul : ∀ h h', rhoF μ (h * h') = rhoF μ h ∘L rhoF μ h' := hF.2.2.2.2.2.1
  have hadjF : ∀ h, ContinuousLinearMap.adjoint (rhoF μ h) = rhoF μ h⁻¹ := hF.2.2.2.2.2.2.2.1
  have hadj : ∀ (u : Pl K) g x y, ⟪rhoL μ u g x, y⟫_ℂ = ⟪x, rhoL μ u g⁻¹ y⟫_ℂ := fun u g x y => by
    have : rhoL μ u g⁻¹ = ContinuousLinearMap.adjoint (rhoL μ u g) := by
      unfold rhoL
      rw [hadjF, map_inv]
    rw [this, ContinuousLinearMap.adjoint_inner_right]
  have hcomZ : ∀ i, Commute (prj Z) (prj (eigL μ (w i) (J i) (χ i))) := fun i =>
    (hB i).2.2.2 (prj Z) fun x _ =>
      (comm_of_stable hZ (rhoL μ (w i) x) (rhoL μ (w i) x⁻¹) (hadj _ x) (hst i x) (hst i x⁻¹)).symm
  have hs : ∀ i, ∀ v ∈ Z, prj (eigL μ (w i) (J i) (χ i)) v ∈ Z := fun i v hv => by
    have h1 : prj Z (prj (eigL μ (w i) (J i) (χ i)) v) = prj (eigL μ (w i) (J i) (χ i)) (prj Z v) :=
      congrArg (fun T : LL μ →L[ℂ] LL μ => T v) (hcomZ i).eq
    rw [prj_self' hZ hv] at h1
    rw [← h1]
    exact prj_mem' hZ _
  have hrho : ∀ i j, i ≠ j → ∀ x y, Commute (rhoL μ (w j) x) (rhoL μ (w i) y) := fun i j hij x y => by
    have hne : w i ≠ w j := fun h => hij (hw h)
    have := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w j)).2.2.2.1 (w i) hne x y
    show rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
    rw [← hmul, ← hmul, this]
  have hcom : ∀ i j, Commute (prj (eigL μ (w i) (J i) (χ i))) (prj (eigL μ (w j) (J j) (χ j))) := fun i j => by
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact (hB j).2.2.2 _ fun x _ => ((hB i).2.2.2 _ fun y _ => hrho i j hij x y).symm
  obtain ⟨p1, p2, p3⟩ := pr_props Z r (fun i => eigL μ (w i) (J i) (χ i)) (fun i => (hB i).1) hcom hs
  have hle : ∀ i, eigL μ (w i) (J i) (χ i) ≤ fixL μ (w i) (kerChr (J i) (χ i) (hc i)) := fun i v hv => by
    refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have h1 : rhoL μ (w i) x v = χ i x • v := by
      simpa [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus] using
        (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv x) hx.1
    have h2 : χ i x = 1 := hx.2
    rw [h2, one_smul] at h1
    exact h1
  refine tr_main (Z := Z) _ R (inf_le_inf_left Z (iInf_mono hle)) inf_le_left hR
    (fun u hu => Submodule.mem_inf.2 ⟨p1 u hu, p2 u⟩) fun u y hy => p3 u y (Submodule.mem_inf.1 hy).2
end

