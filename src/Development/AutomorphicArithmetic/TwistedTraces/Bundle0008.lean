module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.EigenspaceInfSphericalLeClosedInvariant
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

theorem UpperTheory.eigenspace_inf_spherical_le_closed_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (V : Submodule ℂ (LL μ)) (a : TI K n) (x : ℝ) (P : Finset (Pl K)), IsSummand μ V →
        eigIn V (Oinf μ ν a) x ⊓ sphOff μ P ≤ V ∧
        IsClosed ((eigIn V (Oinf μ ν a) x ⊓ sphOff μ P : Submodule ℂ (LL μ)) : Set (LL μ)) ∧
        ∀ w ∈ P, ∀ (g : Gw n w), ∀ u ∈ eigIn V (Oinf μ ν a) x ⊓ sphOff μ P, rhoL μ w g u ∈ eigIn V (Oinf μ ν a) x ⊓ sphOff μ P := by
  intro K _ _ n hn μ _ ν _ V a x P hV
  obtain ⟨m, hm, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  have hO : ∀ h, Commute (Oinf μ ν a) (rhoF μ h) := (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.2.2.2.2.2 a
  have hmul : ∀ (h h' : AdelicGLn.FiniteAdelicGL K n) (u : LL μ), rhoF μ h (rhoF μ h' u) = rhoF μ (h * h') u := by
    intro h h' u
    simp only [rhoF, map_mul, UnitaryRep.map_mul_apply]
  have hmem : ∀ u, u ∈ eigIn V (Oinf μ ν a) x ⊓ sphOff μ P ↔ (u ∈ V ∧ Oinf μ ν a u = (x : ℂ) • u) ∧
      ∀ v ∉ P, ∀ k ∈ GLnLocal.integralGL (v.adicCompletion K) n, rhoL μ v k u = u := by
    intro u
    simp only [eigIn, sphOff, fixL, fixF, rhoL, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff,
      LinearMap.mem_eqLocus, Subgroup.mem_map]
    simp
  refine ⟨fun u hu => ((hmem u).1 hu).1.1, ?_, ?_⟩
  · have : ((eigIn V (Oinf μ ν a) x ⊓ sphOff μ P : Submodule ℂ (LL μ)) : Set (LL μ)) =
        ((V : Set (LL μ)) ∩ {u | Oinf μ ν a u = (x : ℂ) • u}) ∩
          ⋂ v ∈ {v : Pl K | v ∉ P}, ⋂ k ∈ {k | k ∈ GLnLocal.integralGL (v.adicCompletion K) n}, {u | rhoL μ v k u = u} := by
      ext u
      simp only [SetLike.mem_coe, hmem, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [this]
    refine (hV.closed.inter (isClosed_eq (Oinf μ ν a).continuous (continuous_const_smul _))).inter ?_
    exact isClosed_biInter fun v _ => isClosed_biInter fun k _ => isClosed_eq (rhoL μ v k).continuous continuous_id
  · intro w hw g u hu
    obtain ⟨⟨huV, huA⟩, hus⟩ := (hmem u).1 hu
    refine (hmem _).2 ⟨⟨hV.inv _ _ huV, ?_⟩, fun v hv k hk => ?_⟩
    · have := congrArg (fun T : LL μ →L[ℂ] LL μ => T u) (hO (AdelicGLn.localEmbedding w g)).eq
      simp only [mul_apply_eq_comp] at this
      change Oinf μ ν a (rhoF μ _ u) = _
      rw [this, huA, map_smul]
      rfl
    · have hne : w ≠ v := fun e => hv (e ▸ hw)
      have hc := ((UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 v hne.symm g k)
      change rhoF μ _ (rhoF μ _ u) = rhoF μ _ u
      rw [hmul, ← hc, ← hmul]
      have := hus v hv k hk
      rw [rhoL] at this
      rw [this]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsCompactOpenFamilyInfFixedNeBot
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem oneStep {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (Y : Submodule ℂ H)
    (hY : IsClosed (Y : Set H)) (hinv : π.IsInvariant Y) (v : H) (hvY : v ∈ Y) (hv : v ≠ 0) :
    ∃ U : Subgroup G, IsCompact (U : Set G) ∧ IsOpen (U : Set G) ∧
      ∃ y ∈ Y, y ≠ 0 ∧ ∀ u ∈ U, π u y = y := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖v‖ / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrv : r < ‖v‖ := by rw [hr]; linarith
  have hnhds : {g : G | ‖π g v - v‖ < r} ∈ nhds (1 : G) := by
    have hc : Continuous fun g : G => ‖π g v - v‖ :=
      ((π.continuous_orbit v).sub continuous_const).norm
    have ho : IsOpen {g : G | ‖π g v - v‖ < r} := isOpen_lt hc continuous_const
    refine ho.mem_nhds ?_
    simpa using hr0
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hnhds
  refine ⟨(K : Subgroup G), hKc, K.isOpen, ?_⟩
  letI := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨C, hC⟩ : ∃ C : Set H, C = (Y : Set H) ∩ ⋂ u ∈ (K : Subgroup G), Metric.closedBall (π u v) r :=
    ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ C ↔ x ∈ Y ∧ ∀ u ∈ (K : Subgroup G), ‖x - π u v‖ ≤ r := by
    intro x
    simp [hC, dist_eq_norm]
  have hCcl : IsClosed C := by
    rw [hC]
    exact hY.inter (isClosed_biInter fun u _ => Metric.isClosed_closedBall)
  have hconv : Convex ℝ C := by
    rw [hC]
    refine Convex.inter ?_ (convex_iInter₂ fun u _ => convex_closedBall _ _)
    intro a ha b hb s t _ _ _
    exact Y.add_mem (Y.smul_mem (s : ℂ) ha) (Y.smul_mem (t : ℂ) hb)
  have hvC : v ∈ C := by
    refine (hmem v).2 ⟨hvY, fun u hu => ?_⟩
    have : ‖π u v - v‖ < r := hKU hu
    rw [norm_sub_rev]
    exact this.le
  have h0 : (0 : H) ∉ C := by
    intro h
    have := ((hmem 0).1 h).2 1 (one_mem _)
    simp only [UnitaryRep.map_one_apply, zero_sub, norm_neg] at this
    linarith
  have hstab : ∀ x ∈ C, ∀ g ∈ (K : Subgroup G), π g x ∈ C := by
    intro x hx g hg
    obtain ⟨hxY, hxb⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨hinv g x hxY, fun u hu => ?_⟩
    have e : π g x - π u v = π g (x - π (g⁻¹ * u) v) := by
      rw [map_sub, ← UnitaryRep.map_mul_apply, mul_inv_cancel_left]
    rw [e, UnitaryRep.norm_map]
    exact hxb _ (mul_mem (inv_mem hg) hu)
  obtain ⟨y, hyC, hy⟩ := exists_norm_eq_iInf_of_complete_convex ⟨v, hvC⟩ hCcl.isComplete hconv (0 : H)
  have hmin : ∀ w ∈ C, ‖y‖ ≤ ‖w‖ := by
    intro w hw
    have h1 := ciInf_le (f := fun w : C => ‖(0 : H) - (w : H)‖)
      ⟨0, by rintro _ ⟨a, rfl⟩; exact norm_nonneg _⟩ ⟨w, hw⟩
    rw [← hy] at h1
    simpa using h1
  refine ⟨y, ((hmem y).1 hyC).1, fun h => h0 (h ▸ hyC), fun g hg => ?_⟩
  have hz : π g y ∈ C := hstab y hyC g hg
  have hm : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • π g y ∈ C :=
    hconv hyC hz (by norm_num) (by norm_num) (by norm_num)
  have h2 : ‖y‖ ≤ ‖(1 / 2 : ℝ) • y + (1 / 2 : ℝ) • π g y‖ := hmin _ hm
  rw [← smul_add, norm_smul] at h2
  have h3 : 2 * ‖y‖ ≤ ‖y + π g y‖ := by
    have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this] at h2
    linarith
  have hp := parallelogram_law_with_norm ℂ y (π g y)
  rw [UnitaryRep.norm_map] at hp
  have h4 : ‖y - π g y‖ * ‖y - π g y‖ ≤ 0 := by
    nlinarith [norm_nonneg y, norm_nonneg (y + π g y)]
  have h5 : ‖y - π g y‖ = 0 := by
    nlinarith [norm_nonneg (y - π g y)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h5)).symm

theorem UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : ∀ i, UnitaryRep (G i) H), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → ∀ Z : Submodule ℂ H, IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → Z ≠ ⊥ → ∃ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) ∧ (Z ⊓ ⨅ i, fixU (π i) (U i)) ≠ ⊥ := by
  intro r G _ _ _ _ _ _ H _ _ _ π hcomm Z hZ hinv hne
  classical
  have key : ∀ s : Finset (Fin r), ∃ U : ∀ i, Subgroup (G i),
      (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) ∧
        ∃ w ∈ Z, w ≠ 0 ∧ ∀ i ∈ s, ∀ u ∈ U i, π i u w = w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : ∀ i, ∃ K : Subgroup (G i), IsCompact (K : Set (G i)) ∧ IsOpen (K : Set (G i)) :=
        fun i => by
          obtain ⟨K, hK, -⟩ := exists_openSubgroup_isCompact_subset (G := G i) (U := Set.univ)
            Filter.univ_mem
          exact ⟨K, hK, K.isOpen⟩
      choose U hU using h0
      obtain ⟨w, hw, hw0⟩ := Z.ne_bot_iff.mp hne
      exact ⟨U, hU, w, hw, hw0, by simp⟩
    | insert j s hj ih =>
      obtain ⟨U, hU, w, hwZ, hw0, hwf⟩ := ih
      obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule ℂ H, Y = Z ⊓ ⨅ i ∈ s, fixU (π i) (U i) := ⟨_, rfl⟩
      have hmemY : ∀ x, x ∈ Y ↔ x ∈ Z ∧ ∀ i ∈ s, ∀ u ∈ U i, π i u x = x := by
        intro x
        simp [hYdef, Submodule.mem_inf, Submodule.mem_iInf, mem_fixU]
      have hYc : IsClosed (Y : Set H) := by
        have e : (Y : Set H) = (Z : Set H) ∩ ⋂ i ∈ s, (fixU (π i) (U i) : Set H) := by
          ext x
          simp [hYdef, Submodule.mem_inf, Submodule.mem_iInf]
        rw [e]
        exact hZ.inter (isClosed_biInter fun i _ => isClosed_fixU _ _)
      have hYinv : (π j).IsInvariant Y := by
        intro g x hx
        rw [hmemY] at hx ⊢
        refine ⟨hinv j g x hx.1, fun i hi u hu => ?_⟩
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [hcomm i j hij, hx.2 i hi u hu]
      obtain ⟨K, hKc, hKo, y, hyY, hy0, hyf⟩ :=
        oneStep (π j) Y hYc hYinv w ((hmemY w).2 ⟨hwZ, hwf⟩) hw0
      have hyY' := (hmemY y).1 hyY
      refine ⟨Function.update U j K, ?_, y, hyY'.1, hy0, ?_⟩
      · intro i
        by_cases h : i = j
        · subst h
          simpa using And.intro hKc hKo
        · simpa [Function.update_of_ne h] using hU i
      · intro i hi u hu
        by_cases h : i = j
        · subst h
          exact hyf u (by simpa using hu)
        · have hi' : i ∈ s := (Finset.mem_insert.mp hi).resolve_left h
          exact hyY'.2 i hi' u (by simpa [Function.update_of_ne h] using hu)
  obtain ⟨U, hU, w, hwZ, hw0, hwf⟩ := key Finset.univ
  refine ⟨U, hU, fun hbot => hw0 ?_⟩
  have hw : w ∈ Z ⊓ ⨅ i, fixU (π i) (U i) := by
    refine Submodule.mem_inf.mpr ⟨hwZ, ?_⟩
    rw [Submodule.mem_iInf]
    intro i
    exact mem_fixU.mpr (hwf i (Finset.mem_univ i))
  rw [hbot] at hw
  simpa using hw
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.fixedProjection_apply_equivariant_eq :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (hτ : GroundTheory.Automorphic.IsSmooth τ) (π : UnitaryRep G H) (U : Subgroup G) (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) (f : S →ₗ[ℂ] H), Eqv τ π ⊤ f → ∀ x, prj (fixU π U) (f x) = f (fixedProj τ hτ hUc hUo x) := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ π U hUc hUo f hf x
  have hc : (fixU π U).topologicalClosure = fixU π U := (isClosed_fixU π U).submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ (fixU π U).topologicalClosure ↔ v ∈ fixU π U := fun v => by rw [hc]
  have hy : f (fixedProj τ hτ hUc hUo x : S) ∈ fixU π U := fun u hu => by
    rw [← hf.map, (fixedProj τ hτ hUc hUo x).2 u hu]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm _).2 hy) fun b hb => ?_
  have hb' : b ∈ fixU π U := (hm _).1 hb
  rw [← map_sub, ← inner_conj_symm, map_eq_zero_iff _ (starRingEnd ℂ).injective]
  let φ : S →ₗ[ℂ] ℂ := (innerSL ℂ b).toLinearMap ∘ₗ f
  have hφ : ∀ k ∈ U, ∀ v, φ (τ k v) = φ v := fun k hk v => by
    show inner ℂ b (f (τ k v)) = inner ℂ b (f v)
    rw [hf.map, ← ContinuousLinearMap.adjoint_inner_left, UnitaryRep.adjoint_map, hb' _ (U.inv_mem hk)]
  exact coinvariantsKer_le_ker_of_invariant hφ (sub_fixedProj_mem hτ hUc hUo x)
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

private theorem prj_mem_of_closed {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem _ v
  rwa [hc] at h

private theorem prj_eq_of_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (V.le_topologicalClosure hv)

private theorem prj_adjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V :=
  (ContinuousLinearMap.isSelfAdjoint_iff'.1 (isSelfAdjoint_starProjection V.topologicalClosure))

private theorem prj_commute {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H) (h1 : ∀ v ∈ V, T v ∈ V)
    (h2 : ∀ v ∈ V, ContinuousLinearMap.adjoint T v ∈ V) (v : H) : prj V (T v) = T (prj V v) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((hm _).2 (h1 _ (prj_mem_of_closed V hV v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.starProjection_inner_eq_zero v _ ((hm _).2 (h2 w ((hm _).1 hw)))

private theorem prj_fix_commute {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (U : Subgroup G) (T : H →L[ℂ] H)
    (h1 : ∀ g v, π g (T v) = T (π g v))
    (h2 : ∀ g v, π g (ContinuousLinearMap.adjoint T v) = ContinuousLinearMap.adjoint T (π g v)) (v : H) :
    prj (fixU π U) (T v) = T (prj (fixU π U) v) :=
  prj_commute _ (isClosed_fixU π U) T
    (fun v hv u hu => by rw [h1, mem_fixU.1 hv u hu])
    (fun v hv u hu => by rw [h2, mem_fixU.1 hv u hu]) v

theorem UpperTheory.fixedProjection_invariant_and_commuting_reps :
    ∀ (G G' H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (π' : UnitaryRep G' H) (U : Subgroup G) (U' : Subgroup G'), (∀ v, prj (fixU π U) v ∈ fixU π U) ∧ (∀ v ∈ fixU π U, prj (fixU π U) v = v) ∧ (∀ (D : Submodule ℂ H), IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, prj (fixU π U) v ∈ D) ∧ ((∀ g h v, π g (π' h v) = π' h (π g v)) → (∀ h v, prj (fixU π U) (π' h v) = π' h (prj (fixU π U) v)) ∧ ∀ v, prj (fixU π U) (prj (fixU π' U') v) = prj (fixU π' U') (prj (fixU π U) v)) := by
  intro G G' H _ _ _ _ _ _ _ π π' U U'
  refine ⟨prj_mem_of_closed _ (isClosed_fixU π U), fun v hv => prj_eq_of_mem _ hv, ?_, ?_⟩
  · intro D hD hinv v hv
    have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
    have hcomm : ∀ g v, π g (prj D v) = prj D (π g v) := fun g v => by
      have hi : π.IsInvariant D.topologicalClosure := by rw [hc]; exact hinv
      exact congrArg (fun T : H →L[ℂ] H => T v)
        ((UnitaryRep.isInvariant_iff_commute_starProjection D.topologicalClosure).1 hi g).eq
    have h := prj_fix_commute π U (prj D) hcomm (fun g v => by rw [prj_adjoint]; exact hcomm g v) v
    rw [prj_eq_of_mem D hv] at h
    rw [h]
    exact prj_mem_of_closed D hD _
  · intro hc
    have h4 : ∀ h v, prj (fixU π U) (π' h v) = π' h (prj (fixU π U) v) := fun h v =>
      prj_fix_commute π U (π' h) (fun g v => hc g h v)
        (fun g v => by rw [UnitaryRep.adjoint_map]; exact hc g h⁻¹ v) v
    refine ⟨h4, fun v => ?_⟩
    have h4' : ∀ g v, prj (fixU π' U') (π g v) = π g (prj (fixU π' U') v) := fun g v =>
      prj_fix_commute π' U' (π g) (fun h v => (hc g h v).symm)
        (fun h v => by rw [UnitaryRep.adjoint_map]; exact (hc g⁻¹ h v).symm) v
    exact prj_fix_commute π U (prj (fixU π' U')) (fun g v => (h4' g v).symm)
      (fun g v => by rw [prj_adjoint]; exact (h4' g v).symm) v
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IntegralOperatorFixedInvariantOfLeftInvariantKer
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

theorem UpperTheory.integralOperator_fixed_invariant_of_left_invariant_kernel :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (π : UnitaryRep G H) (τ : Representation ℂ G S) (m : Measure G) [m.IsMulLeftInvariant] (φ : G → ℂ) (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S) (U : Subgroup G), IsOp π m φ T → IsIntegralOp m τ φ A → (∀ u ∈ U, ∀ g, φ (u * g) = φ g) → (∀ v, T v ∈ fixU π U) ∧ (∀ x, A x ∈ fixedVectors τ U) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ B : H →L[ℂ] H, (∀ g v, π g (B v) = B (π g v)) → (∀ g v, π g (ContinuousLinearMap.adjoint B v) = ContinuousLinearMap.adjoint B (π g v)) → ∀ v, T (B v) = B (T v)) ∧ ∀ f : S →ₗ[ℂ] H, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x) := by
  intro G H S _ _ _ _ _ _ _ _ _ _ π τ m _ φ T A U hT hA hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v u hu
    refine ext_inner_left ℂ fun y => ?_
    rw [UnitaryRep.inner_map_right, hT, hT]
    rw [← integral_mul_left_eq_self (fun g => φ g * ⟪y, π g v⟫_ℂ) u]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪π u⁻¹ y, π g v⟫_ℂ = φ (u * g) * ⟪y, π (u * g) v⟫_ℂ
    rw [hφ u hu g, UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right π u]
  · intro x u hu
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 : l (τ u (A x)) = (l ∘ₗ τ u) (A x) := rfl
    rw [map_sub, h1, (hA x (l ∘ₗ τ u)).2, (hA x l).2, sub_eq_zero]
    rw [← integral_mul_left_eq_self (fun g => φ g * l (τ g x)) u]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * l (τ u (τ g x)) = φ (u * g) * l (τ (u * g) x)
    rw [hφ u hu g, map_mul, Module.End.mul_apply]
  · intro D hD hinv v hv
    have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
    rw [← hc, ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro y hy
    rw [hT]
    have : ∀ g, φ g * ⟪y, π g v⟫_ℂ = 0 := fun g => by
      rw [(Submodule.mem_orthogonal' D y).1 hy _ (hinv g v hv), mul_zero]
    simp [this]
  · intro B hB _ v
    refine ext_inner_left ℂ fun y => ?_
    rw [hT, ← ContinuousLinearMap.adjoint_inner_left, hT]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪y, π g (B v)⟫_ℂ = φ g * ⟪ContinuousLinearMap.adjoint B y, π g v⟫_ℂ
    rw [hB, ContinuousLinearMap.adjoint_inner_left]
  · intro f hf x
    refine ext_inner_left ℂ fun y => ?_
    have h1 : ⟪y, f (A x)⟫_ℂ = ((innerSL ℂ y).toLinearMap ∘ₗ f) (A x) := rfl
    rw [hT, h1, (hA x _).2]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪y, π g (f x)⟫_ℂ = φ g * ⟪y, f (τ g x)⟫_ℂ
    rw [hf.map]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubspaceProductClosed
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_res {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Submodule ℂ H) :
    ∀ (r : ℕ) (T : Fin r → H →L[ℂ] H) (t : Fin r → Module.End ℂ X), (∀ i (v : X), ((t i v : X) : H) = T i v) →
      ∀ v : X, (((List.ofFn t).prod v : X) : H) = (List.ofFn T).prod v := by
  intro r
  induction r with
  | zero => intro T t _ v; simp
  | succ r ih =>
    intro T t h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, h,
      ih (fun i => T i.succ) (fun i => t i.succ) (fun i => h _) v]
    rfl

set_option maxHeartbeats 800000 in
theorem UpperTheory.isotypic_subspace_product_closed :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (U : ∀ i, Subgroup (G i)) (c : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) (T : Fin r → H →L[ℂ] H) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) f → ∀ (x : fixedVectors (τ i) (U i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = f (t x)) → (∀ i, (Z ⊓ ⨅ i, fixU (π i) (U i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) (U i)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x : fixedVectors (τ i) (U i), T i (f x) = f (B i x)) → ∀ v : ↥(Z ⊓ ⨅ i, fixU (π i) (U i)), (((List.ofFn fun i => c i (B i)).prod v : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = (List.ofFn T).prod v := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z U c T B hc1 hle hB
  let X : Submodule ℂ H := Z ⊓ ⨅ i, fixU (π i) (U i)
  have hX : X = Z ⊓ ⨅ i, fixU (π i) (U i) := rfl
  let D : Fin r → Submodule ℂ H := fun i => Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)
  have hD : ∀ i v, v ∈ D i ↔ v ∈ Z ∧ ∀ j, j ≠ i → v ∈ fixU (π j) (U j) := fun i v => by
    simp only [D, Submodule.mem_inf, Submodule.mem_iInf]
  have hXD : ∀ i, X = D i ⊓ fixU (π i) (U i) := fun i => by
    ext v
    simp only [hX, Submodule.mem_inf, Submodule.mem_iInf, hD]
    refine ⟨fun h => ⟨⟨h.1, fun j _ => h.2 j⟩, h.2 i⟩, fun h => ⟨h.1.1, fun j => ?_⟩⟩
    by_cases e : j = i
    · exact e ▸ h.2
    · exact h.1.2 j e
  have hm : ∀ i f, Eqv (τ i) (π i) (D i) f → ∀ x : fixedVectors (τ i) (U i), f x ∈ X := fun i f hf x => by
    rw [hXD i]
    exact ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  refine prod_res X r T _ fun i v => ?_
  have key : ∀ y ∈ spanFix (τ i) (π i) (D i) (U i), ∃ h : y ∈ X, ((c i (B i) ⟨y, h⟩ : X) : H) = T i y := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      exact ⟨hm i f hf ⟨x, hx⟩, (hc1 i (B i) f hf ⟨x, hx⟩ _ rfl).trans (hB i f ⟨fun _ => trivial, hf.map⟩ ⟨x, hx⟩).symm⟩
    | zero => exact ⟨X.zero_mem, (congrArg Subtype.val (map_zero (c i (B i)))).trans (map_zero (T i)).symm⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      refine ⟨X.add_mem a b, (congrArg Subtype.val (map_add (c i (B i)) ⟨u, a⟩ ⟨v, b⟩)).trans ?_⟩
      rw [map_add (f := _), ← ha, ← hb]; rfl
    | smul k u _ h1 =>
      obtain ⟨a, ha⟩ := h1
      refine ⟨X.smul_mem k a, (congrArg Subtype.val (map_smul (c i (B i)) k ⟨u, a⟩)).trans ?_⟩
      rw [map_smul, ← ha]; rfl
  exact (key v (hle i v.2)).2
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IwahoriCompactOpenAndIwCosetIndicatorTest
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Pointwise

private theorem iwCoset_eq_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    iwCoset w ν = ((GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) *
        ({Cartan.diagPow (w.adicCompletion K) n ν} : Set (Gw n w))) *
      (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
  · rintro ⟨x, ⟨a, ha, d, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

private theorem isOpen_iwCoset {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    IsOpen (iwCoset w ν) := by
  rw [iwCoset_eq_mul]
  exact (GLnLocal.isOpen_iwahori (w.adicCompletion K) n).mul_left

private theorem isCompact_iwCoset {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    IsCompact (iwCoset w ν) := by
  rw [iwCoset_eq_mul]
  have hI := GLnLocal.isCompact_iwahori (w.adicCompletion K) n
  exact (hI.mul isCompact_singleton).mul hI

theorem UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K),
        CO (GLnLocal.iwahori (w.adicCompletion K) n) ∧
        (∀ U : Subgroup (Gw n w), IsOpen (U : Set (Gw n w)) → U ≤ GLnLocal.integralGL (w.adicCompletion K) n → CO U) ∧
        ∀ ν : Fin n → ℤ, Test ((iwCoset w ν).indicator 1 : Gw n w → ℂ) ∧
          ∀ u ∈ GLnLocal.iwahori (w.adicCompletion K) n, ∀ g : Gw n w,
            (iwCoset w ν).indicator (1 : Gw n w → ℂ) (u * g) = (iwCoset w ν).indicator (1 : Gw n w → ℂ) g := by
  intro K _ _ n w
  refine ⟨⟨GLnLocal.isCompact_iwahori _ n, GLnLocal.isOpen_iwahori _ n⟩, ?_, ?_⟩
  · intro U ho hle
    exact ⟨(GLnLocal.isCompact_integralGL _ n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ ho) hle, ho⟩
  · intro ν
    have hc := isCompact_iwCoset w ν
    have hclopen : IsClopen (iwCoset w ν) := ⟨hc.isClosed, isOpen_iwCoset w ν⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ iwCoset w ν
      · filter_upwards [hclopen.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
        rfl
      · filter_upwards [hclopen.compl.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
    · intro u hu g
      have hiff : u * g ∈ iwCoset w ν ↔ g ∈ iwCoset w ν := by
        constructor
        · rintro ⟨a, ha, b, hb, h⟩
          refine ⟨u⁻¹ * a, mul_mem (inv_mem hu) ha, b, hb, ?_⟩
          calc g = u⁻¹ * (u * g) := (inv_mul_cancel_left u g).symm
            _ = _ := by rw [h]; simp only [mul_assoc]
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨u * a, mul_mem hu ha, b, hb, by simp only [mul_assoc]⟩
      by_cases hg : g ∈ iwCoset w ν
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]
        rfl
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hiff.1 h))]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.LocalHeckeOperatorMemOfClosedInvariant
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

theorem UpperTheory.localHeckeOperator_mem_of_closed_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) [MeasurableSpace (Gw n w)] (m : Measure (Gw n w))
        (φ : Gw n w → ℂ) (T : LL μ →L[ℂ] LL μ) (Z : Submodule ℂ (LL μ)), IsClosed (Z : Set (LL μ)) →
        (∀ (g : Gw n w), ∀ v ∈ Z, rhoL μ w g v ∈ Z) → IsOloc μ w m φ T → ∀ v ∈ Z, T v ∈ Z := by
  intro K _ _ n μ _ w _ m φ T Z hZ hst hT v hv
  haveI : CompleteSpace Z := hZ.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal Z, Submodule.mem_orthogonal]
  intro u hu
  rw [hT u v]
  have h0 : ∀ g : Gw n w, φ g * inner ℂ u (rhoL μ w g v) = 0 := fun g => by
    rw [(Submodule.mem_orthogonal' _ _).1 hu _ (hst g v hv), mul_zero]
  simp only [h0, integral_zero]
end

