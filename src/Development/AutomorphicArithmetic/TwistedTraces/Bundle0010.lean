module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0001
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.EigenspaceCompLevelProjectionEqInfFixed
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

theorem UpperTheory.eigenspace_comp_levelProjection_eq_inf_fixed :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (V : Submodule ℂ (LL μ)) (a : TI K n) (x : ℝ) (P : Finset (Pl K)) (Uv : ∀ v : Pl K, Subgroup (Gw n v)), x ≠ 0 →
        eigIn V (Oinf μ ν a ∘L prj (fixF μ (levOn P Uv))) x =
          (eigIn V (Oinf μ ν a) x ⊓ sphOff μ P) ⊓ ⨅ v ∈ P, fixL μ v (Uv v) := by
  intro K _ _ n hn μ _ ν _ V a x P Uv hx
  obtain ⟨-, hmem, hp1, hp2, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (levOn P Uv)
  obtain ⟨m, hm, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  haveI := hm
  have hcomm : ∀ h, Commute (Oinf μ ν a) (rhoF μ h) := fun h =>
    (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.2.2.2.2.2 a h
  have hpres : ∀ v ∈ fixF μ (levOn P Uv), Oinf μ ν a v ∈ fixF μ (levOn P Uv) := fun v hv => by
    refine (hmem _).2 fun u hu => ?_
    have h1 : rhoF μ u (Oinf μ ν a v) = Oinf μ ν a (rhoF μ u v) :=
      (DFunLike.congr_fun (hcomm u) v).symm
    rw [h1, (hmem v).1 hv u hu]
  have hfix := UpperTheory.ConvolutionTheory.C.fixLev K n μ P Uv
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  ext w
  have hE : ∀ (A : LL μ →L[ℂ] LL μ), w ∈ eigIn V A x ↔ w ∈ V ∧ A w = (x : ℂ) • w := fun A => by
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have hF : w ∈ fixF μ (levOn P Uv) ↔ w ∈ sphOff μ P ∧ w ∈ ⨅ v ∈ P, fixL μ v (Uv v) := by
    rw [hfix, Submodule.mem_inf]
  rw [Submodule.mem_inf, Submodule.mem_inf, hE, hE]
  constructor
  · rintro ⟨hV, hA⟩
    have hA' : Oinf μ ν a (prj (fixF μ (levOn P Uv)) w) = (x : ℂ) • w := hA
    have hw : w ∈ fixF μ (levOn P Uv) := by
      have h1 : w = (x : ℂ)⁻¹ • Oinf μ ν a (prj (fixF μ (levOn P Uv)) w) := by
        rw [hA', smul_smul, inv_mul_cancel₀ hx', one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (hpres _ (hp1 w))
    rw [hp2 w hw] at hA'
    exact ⟨⟨⟨hV, hA'⟩, (hF.1 hw).1⟩, (hF.1 hw).2⟩
  · rintro ⟨⟨⟨hV, hA⟩, h1⟩, h2⟩
    refine ⟨hV, ?_⟩
    show Oinf μ ν a (prj (fixF μ (levOn P Uv)) w) = (x : ℂ) • w
    rw [hp2 w (hF.2 ⟨h1, h2⟩), hA]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsAlgHomEndFixedVectorsToFixedSubspace
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.exists_algHom_end_fixedVectors_to_fixed_subspace :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (hτ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (U : Subgroup G) (_ : IsCompact (U : Set G)) (_ : IsOpen (U : Set G)) (D X : Submodule ℂ H) [FiniteDimensional ℂ X] [FiniteDimensional ℂ (fixedVectors τ U)] [Nontrivial (fixedVectors τ U)], IsClosed (D : Set H) → π.IsInvariant D → X = D ⊓ fixU π U → X ≤ spanFix τ π D U → ∃ c : Module.End ℂ (fixedVectors τ U) →ₐ[ℂ] Module.End ℂ X, (∀ t f, Eqv τ π D f → ∀ (x : fixedVectors τ U) (y : X), (y : H) = f x → ((c t y : X) : H) = f (t x)) ∧ ∀ t, c t ∈ Algebra.adjoin ℂ {a : Module.End ℂ X | ∃ g, ∀ v : X, ((a v : X) : H) = prj (fixU π U) (π g v)} := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π U hUc hUo D X _ _ _ hD hinv hX hle
  subst hX
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π U U
  have hm : ∀ f, Eqv τ π D f → ∀ x : fixedVectors τ U, f x ∈ D ⊓ fixU π U := fun f hf x =>
    ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  let res : ∀ f, Eqv τ π D f → fixedVectors τ U →ₗ[ℂ] ↥(D ⊓ fixU π U) := fun f hf =>
    (f ∘ₗ (fixedVectors τ U).subtype).codRestrict _ (hm f hf)
  let e : S →ₗ[ℂ] fixedVectors τ U := fixedProj τ hτ hUc hUo
  let b : G → Module.End ℂ (fixedVectors τ U) := fun g => e ∘ₗ τ g ∘ₗ (fixedVectors τ U).subtype
  let a : G → Module.End ℂ ↥(D ⊓ fixU π U) := fun g =>
    ((prj (fixU π U) ∘L π g).toLinearMap ∘ₗ (D ⊓ fixU π U).subtype).codRestrict _ fun v =>
      ⟨p3 D hD hinv _ (hinv g _ v.2.1), p1 _⟩
  obtain ⟨c, h1, h2⟩ := UpperTheory.exists_algHom_end_intertwining_mem_adjoin (fixedVectors τ U) ↥(D ⊓ fixU π U) {k | ∃ f hf, k = res f hf}
    (Set.range fun g => (b g, a g)) (by
      rw [eq_top_iff]
      rintro ⟨y, hy⟩ -
      have h3 : spanFix τ π D U ≤ (⨆ k ∈ {k | ∃ f hf, k = res f hf}, LinearMap.range k).map (D ⊓ fixU π U).subtype := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨f, hf, x, hx, rfl⟩
        exact ⟨res f hf ⟨x, hx⟩, Submodule.mem_iSup_of_mem (res f hf) (Submodule.mem_iSup_of_mem ⟨f, hf, rfl⟩ ⟨_, rfl⟩), rfl⟩
      obtain ⟨z, hz, e⟩ := h3 (hle hy)
      exact (Subtype.ext e : z = ⟨y, hy⟩) ▸ hz) (by
      rintro _ ⟨g, rfl⟩ _ ⟨f, hf, rfl⟩
      refine LinearMap.ext fun x => Subtype.ext ?_
      show prj (fixU π U) (π g (f x)) = f (fixedProj τ hτ hUc hUo (τ g x))
      rw [← hf.map]
      exact UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π U hUc hUo f ⟨fun _ => trivial, hf.map⟩ _) (by
      intro x hx
      let W : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
        refine (Submodule.map_span_le (τ g) _ _).2 ?_ (Submodule.mem_map_of_mem hv)
        rintro _ ⟨h, rfl⟩
        exact Submodule.subset_span ⟨g * h, by simp⟩⟩
      have hW : Submodule.span ℂ (Set.range fun g => τ g x) = ⊤ := by
        rcases eq_bot_or_eq_top W with h | h
        · have h' : Submodule.span ℂ (Set.range fun g => τ g x) = ⊥ := congrArg Subrepresentation.toSubmodule h
          have : τ 1 x ∈ Submodule.span ℂ (Set.range fun g => τ g x) := Submodule.subset_span ⟨1, rfl⟩
          rw [h', map_one] at this
          exact (hx (Subtype.ext this)).elim
        · exact congrArg Subrepresentation.toSubmodule h
      rw [eq_top_iff]
      rintro y -
      have h4 : e y = y := Subtype.ext (fixedProj_apply_of_mem hτ hUc hUo y.2)
      rw [← h4]
      refine (Submodule.map_span_le e (Set.range fun g => τ g x) _).2 ?_ (Submodule.mem_map_of_mem (hW ▸ Submodule.mem_top))
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span ⟨_, ⟨g, rfl⟩, rfl⟩)
  refine ⟨c, fun t f hf x y hy => ?_, fun t => Algebra.adjoin_mono ?_ (h2 t)⟩
  · obtain rfl : y = res f hf x := Subtype.ext hy
    exact congrArg Subtype.val (LinearMap.congr_fun (h1 t _ ⟨f, hf, rfl⟩) x)
  · rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, fun _ => rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalFixedVectorsIsotypicOfIrreducib
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (K : Subgroup G), IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K) → fixedVectors τ K ≠ ⊥ → ∀ t : Module.End ℂ (fixedVectors τ K), ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ ∀ x : fixedVectors τ K, A x = t x := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π K hKc hKo hfd hne t
  haveI := hfd
  haveI : Nontrivial (fixedVectors τ K) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let b : G → Module.End ℂ (fixedVectors τ K) := fun g => e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype
  have he : ∀ y : fixedVectors τ K, e y = y := fun y =>
    Subtype.ext (fixedProj_apply_of_mem hτ hKc hKo y.2)
  have hq : ∀ f, Eqv τ π ⊤ f → ∀ x, prj (fixU π K) (f x) = f (e x) := fun f hf x =>
    UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf x
  have hcomm : ∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H),
      (∀ g h v, π g (π' h v) = π' h (π g v)) →
        ∀ h v, prj (fixU π K) (π' h v) = π' h (prj (fixU π K) v) := by
    intro G' _ _ π' hc
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1
  have htop : Algebra.adjoin ℂ (Set.range b) = ⊤ := by
    obtain ⟨c, h1, h2⟩ := UpperTheory.exists_algHom_end_intertwining_mem_adjoin (fixedVectors τ K) (fixedVectors τ K) {LinearMap.id}
      (Set.range fun g => (b g, b g)) (by simp) (by
        rintro _ ⟨g, rfl⟩ _ rfl
        rfl) (by
        intro x hx
        let W : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
          refine (Submodule.map_span_le (τ g) _ _).2 ?_ (Submodule.mem_map_of_mem hv)
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp⟩⟩
        have hW : Submodule.span ℂ (Set.range fun g => τ g x) = ⊤ := by
          rcases eq_bot_or_eq_top W with h | h
          · have h' : Submodule.span ℂ (Set.range fun g => τ g x) = ⊥ := congrArg Subrepresentation.toSubmodule h
            have : τ 1 x ∈ Submodule.span ℂ (Set.range fun g => τ g x) := Submodule.subset_span ⟨1, rfl⟩
            rw [h', map_one] at this
            exact (hx (Subtype.ext this)).elim
          · exact congrArg Subrepresentation.toSubmodule h
        rw [eq_top_iff]
        rintro y -
        rw [← he y]
        refine (Submodule.map_span_le e (Set.range fun g => τ g x) _).2 ?_ (Submodule.mem_map_of_mem (hW ▸ Submodule.mem_top))
        rintro _ ⟨g, rfl⟩
        exact Submodule.subset_span ⟨_, ⟨g, rfl⟩, rfl⟩)
    rw [eq_top_iff]
    intro s _
    have hcs : c s = s := by simpa using h1 s LinearMap.id rfl
    rw [← hcs]
    refine Algebra.adjoin_mono ?_ (h2 s)
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  have ht : t ∈ Algebra.adjoin ℂ (Set.range b) := by rw [htop]; trivial
  induction ht using Algebra.adjoin_induction with
  | mem s hs =>
    obtain ⟨g, rfl⟩ := hs
    refine ⟨prj (fixU π K) ∘L π g ∘L prj (fixU π K),
      (fixedVectors τ K).subtype ∘ₗ e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype ∘ₗ e,
      ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact p3 D hD hinv _ (hinv g _ (p3 D hD hinv _ hv))
    · intro G' _ _ π' hc h v
      show prj (fixU π K) (π g (prj (fixU π K) (π' h v))) = π' h (prj (fixU π K) (π g (prj (fixU π K) v)))
      rw [hcomm G' π' hc h v, hc, hcomm G' π' hc]
    · intro f hf x
      show prj (fixU π K) (π g (prj (fixU π K) (f x))) = f (e (τ g (e x)))
      rw [hq f hf x, ← hf.map, hq f hf]
    · intro x
      show ((e (τ g ((e (x : S) : fixedVectors τ K) : S)) : fixedVectors τ K) : S) = _
      rw [he x]
      rfl
  | algebraMap z =>
    refine ⟨z • prj (fixU π K), z • ((fixedVectors τ K).subtype ∘ₗ e),
      ⟨fun v => (fixU π K).smul_mem z (p1 v), fun x => (fixedVectors τ K).smul_mem z (e x).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.smul_mem z (p3 D hD hinv _ hv)
    · intro G' _ _ π' hc h v
      show z • prj (fixU π K) (π' h v) = π' h (z • prj (fixU π K) v)
      rw [hcomm G' π' hc h v, map_smul]
    · intro f hf x
      show z • prj (fixU π K) (f x) = f (z • ((e x : fixedVectors τ K) : S))
      rw [hq f hf x, map_smul]
    · intro x
      show z • ((e (x : S) : fixedVectors τ K) : S) = _
      rw [he x]
      simp [Module.algebraMap_end_apply]
  | add s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ + T₂, A₁ + A₂, ⟨fun v => (fixU π K).add_mem (a1 v) (b1 v),
      fun x => (fixedVectors τ K).add_mem (a2 x) (b2 x), ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.add_mem (a3 D hD hinv v hv) (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (π' h v) + T₂ (π' h v) = π' h (T₁ v + T₂ v)
      rw [a4 G' π' hc, b4 G' π' hc, map_add (f := _)]
    · intro f hf x
      show T₁ (f x) + T₂ (f x) = f (A₁ x + A₂ x)
      rw [a5 f hf, b5 f hf, map_add (f := _)]
    · intro x
      show A₁ x + A₂ x = _
      rw [a6 x, b6 x]
      rfl
  | mul s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ ∘L T₂, A₁ ∘ₗ A₂, ⟨fun v => a1 _, fun x => a2 _, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact a3 D hD hinv _ (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (T₂ (π' h v)) = π' h (T₁ (T₂ v))
      rw [b4 G' π' hc, a4 G' π' hc]
    · intro f hf x
      show T₁ (T₂ (f x)) = f (A₁ (A₂ x))
      rw [b5 f hf, a5 f hf]
    · intro x
      show A₁ (A₂ x) = _
      rw [b6 x, a6 (u x)]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.InfFixedLeSpanFixOfDenseSpanAll
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.inf_fixed_le_spanFix_of_dense_spanAll :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (π : UnitaryRep G H) (U : Subgroup G) (_ : IsCompact (U : Set G)) (_ : IsOpen (U : Set G)) (V D : Submodule ℂ H), IsClosed (D : Set H) → π.IsInvariant D → D ≤ V → V ≤ (spanAll τ π V).topologicalClosure → FiniteDimensional ℂ ↥(D ⊓ fixU π U) → D ⊓ fixU π U ≤ spanFix τ π D U := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ π U hUc hUo V D hD hinv hDV hV hfin y hy
  have hQX : spanFix τ π D U ≤ D ⊓ fixU π U := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, x, hx, rfl⟩
    exact ⟨hf.mem x, fun u hu => by rw [← hf.map, hx u hu]⟩
  haveI : FiniteDimensional ℂ ↥(spanFix τ π D U) := Submodule.finiteDimensional_of_le hQX
  have hQc : IsClosed (spanFix τ π D U : Set H) := Submodule.closed_of_finiteDimensional _
  have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
  have hpm : ∀ v, prj D v ∈ D := fun v => by
    have h : prj D v ∈ D.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hc] at h
  have hpc : ∀ g v, π g (prj D v) = prj D (π g v) := fun g v => by
    have hi : π.IsInvariant D.topologicalClosure := by rw [hc]; exact hinv
    exact congrArg (fun T : H →L[ℂ] H => T v)
      ((UnitaryRep.isInvariant_iff_commute_starProjection D.topologicalClosure).1 hi g).eq
  let Φ : H →L[ℂ] H := prj (fixU π U) ∘L prj D
  have hspan : spanAll τ π V ≤ (spanFix τ π D U).comap (Φ : H →ₗ[ℂ] H) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, x, rfl⟩
    let f' : S →ₗ[ℂ] H := (prj D : H →ₗ[ℂ] H) ∘ₗ f
    have hmap : ∀ g x, f' (τ g x) = π g (f' x) := fun g x => by
      show prj D (f (τ g x)) = π g (prj D (f x))
      rw [hf.map, hpc]
    have hf1 : Eqv τ π D f' := ⟨fun x => hpm _, hmap⟩
    have hf2 : Eqv τ π ⊤ f' := ⟨fun _ => trivial, hmap⟩
    have h := UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π U hUc hUo f' hf2 x
    show prj (fixU π U) (prj D (f x)) ∈ spanFix τ π D U
    have h' : prj (fixU π U) (prj D (f x)) = f' (fixedProj τ hτ hUc hUo x) := h
    rw [h']
    exact Submodule.subset_span ⟨f', hf1, _, (fixedProj τ hτ hUc hUo x).2, rfl⟩
  have hcl : (spanAll τ π V).topologicalClosure ≤ (spanFix τ π D U).comap (Φ : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hspan (hQc.preimage Φ.continuous)
  have hy' : Φ y ∈ spanFix τ π D U := hcl (hV (hDV hy.1))
  have hp : prj D y = y := Submodule.starProjection_eq_self_iff.2 (D.le_topologicalClosure hy.1)
  have he : prj (fixU π U) y = y := (UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π U U).2.1 y hy.2
  have hΦ : Φ y = y := by
    show prj (fixU π U) (prj D y) = y
    rw [hp, he]
  rwa [hΦ] at hy'
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IsotypicProjectionProductCommute
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_projection_product_commute :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∃ f', Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f' ∧ ∀ x, R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (f x)) = f' (I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
  let a : Fin r → (H →L[ℂ] H) := fun j => prj (fixU (π j) (L j))
  have hcomm : ∀ p q, p ≠ q → Commute (a p) (a q) := fun p q hpq => by
    refine ContinuousLinearMap.ext fun v => ?_
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G p) (G q) H (π p) (π q) (L p) (L q)).2.2.2 (hc p q hpq)).2 v
  have hact : ∀ j, j ≠ i → ∀ g v, a j (π i g v) = π i g (a j v) := fun j hj g v =>
    ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (L j) (L i)).2.2.2 (hc j i hj)).1 g v
  obtain ⟨hprod, hQc⟩ := UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r a hcomm i
  let b : Fin r → (H →L[ℂ] H) := Function.update a i 1
  let Q : H →L[ℂ] H := (List.ofFn b).prod
  have hQa : Commute (a i) Q := hQc (a i) fun j hj => hcomm i j hj.symm
  have hQπ : ∀ g v, Q (π i g v) = π i g (Q v) := fun g v => by
    have h : Commute (π i g : H →L[ℂ] H) Q := hQc _ fun j hj => by
      refine ContinuousLinearMap.ext fun v => ?_
      exact (hact j hj g v).symm
    exact (congrArg (fun T : H →L[ℂ] H => T v) h.eq).symm
  have hb : ∀ p q, p ≠ q → Commute (b p) (b q) := fun p q hpq => by
    by_cases hp : p = i
    · subst hp
      simp only [b, Function.update_self]
      exact Commute.one_left _
    · by_cases hq : q = i
      · subst hq
        simp only [b, Function.update_self]
        exact Commute.one_right _
      · simp only [b, Function.update_of_ne hp, Function.update_of_ne hq]
        exact hcomm p q hpq
  have hQZ : ∀ v ∈ Z, Q v ∈ Z := by
    let M : Submonoid (H →L[ℂ] H) :=
      { carrier := {T | ∀ v ∈ Z, T v ∈ Z}
        mul_mem' := fun ha hb v hv => ha _ (hb v hv)
        one_mem' := fun v hv => hv }
    have hM : Q ∈ M := by
      refine Submonoid.list_prod_mem M fun x hx => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      by_cases hj : j = i
      · subst hj
        simp only [b, Function.update_self]
        exact M.one_mem
      · simp only [b, Function.update_of_ne hj]
        exact fun v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).2.2.1 Z hZc (hZi j) v hv
    exact hM
  have hQfix : ∀ j, j ≠ i → ∀ v, Q v ∈ fixU (π j) (L j) := fun j hj v => by
    have h := (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r b hb j).1
    have h2 : Q v = a j ((List.ofFn (Function.update b j 1)).prod v) := by
      have h3 : b j = a j := Function.update_of_ne hj _ _
      change (List.ofFn b).prod v = _
      rw [h, h3]
      rfl
    rw [h2]
    exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).1 _
  let f' : S i →ₗ[ℂ] H := (R : H →ₗ[ℂ] H) ∘ₗ (Q : H →ₗ[ℂ] H) ∘ₗ f ∘ₗ ((I i).symm : S i →ₗ[ℂ] S i)
  have hf' : ∀ y, f' y = R (Q (f ((I i).symm y))) := fun y => rfl
  have hfZ : ∀ x, f x ∈ Z := fun x => (Submodule.mem_inf.1 (hf.mem x)).1
  refine ⟨f', ⟨fun y => ?_, fun g y => ?_⟩, fun x => ?_⟩
  · rw [hf']
    have hw := hQZ _ (hfZ ((I i).symm y))
    refine Submodule.mem_inf.2 ⟨hRZ _ hw, ?_⟩
    simp only [Submodule.mem_iInf]
    intro j hj u hu
    have h := hRs j ((s j).symm u) _ hw
    rw [(s j).apply_symm_apply] at h
    rw [← h, hQfix j hj _ _ (hsK j u hu)]
  · have hIs : (I i).symm (τ i g y) = τ i ((s i).symm g) ((I i).symm y) := by
      apply (I i).injective
      rw [hI, (I i).apply_symm_apply, (I i).apply_symm_apply, (s i).apply_symm_apply]
    rw [hf', hf', hIs, hf.map, hQπ, hRs i _ _ (hQZ _ (hfZ _)), (s i).apply_symm_apply]
  · have hE : Eqv (τ i) (π i) ⊤ f := ⟨fun _ => Submodule.mem_top, hf.map⟩
    have h1 := UpperTheory.fixedProjection_apply_equivariant_eq (G i) H (S i) (τ i) (hsm i) (π i) (L i) (hL i).1 (hL i).2 f hE x
    have h2 : (List.ofFn a).prod (f x) = Q (a i (f x)) := by
      rw [hprod]
      exact congrArg (fun T : H →L[ℂ] H => T (f x)) hQa.eq
    rw [hf', (I i).symm_apply_apply]
    change R ((List.ofFn a).prod (f x)) = _
    rw [h2]
    change R (Q (prj (fixU (π i) (L i)) (f x))) = _
    rw [h1]
end

