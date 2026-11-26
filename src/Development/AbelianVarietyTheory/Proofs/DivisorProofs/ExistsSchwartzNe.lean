module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.Adapt

section Glue

variable {κ κ₀ κ₁ : Type} (ε : κ ≃ κ₀ ⊕ κ₁)

def glue {R : Type} (a : κ₀ → R) (b : κ₁ → R) : κ → R := fun k => Sum.elim a b (ε k)

@[simp] theorem glue_inl {R : Type} (a : κ₀ → R) (b : κ₁ → R) (k : κ₀) : glue ε a b (ε.symm (.inl k)) = a k := by
  simp [glue]

@[simp] theorem glue_inr {R : Type} (a : κ₀ → R) (b : κ₁ → R) (k : κ₁) : glue ε a b (ε.symm (.inr k)) = b k := by
  simp [glue]

theorem glue_map {R S : Type} (f : R → S) (a : κ₀ → R) (b : κ₁ → R) :
    (fun k => f (glue ε a b k)) = glue ε (fun k => f (a k)) fun k => f (b k) := by
  funext k; unfold glue; cases ε k <;> rfl

theorem glue_add {R : Type} [Add R] (a a' : κ₀ → R) (b b' : κ₁ → R) :
    glue ε a b + glue ε a' b' = glue ε (a + a') (b + b') := by
  funext k; simp only [glue, Pi.add_apply]; cases ε k <;> rfl

theorem glue_smul {R S : Type} [SMul S R] (c : S) (a : κ₀ → R) (b : κ₁ → R) :
    c • glue ε a b = glue ε (c • a) (c • b) := by
  funext k; simp only [glue, Pi.smul_apply]; cases ε k <;> rfl

theorem glue_zero {R : Type} [Zero R] : glue ε (0 : κ₀ → R) 0 = 0 := by
  funext k; simp only [glue]; cases ε k <;> rfl

theorem exists_glue {R : Type} (x : κ → R) : ∃ a b, x = glue ε a b :=
  ⟨fun k => x (ε.symm (.inl k)), fun k => x (ε.symm (.inr k)), funext fun k => by
    obtain ⟨k, rfl⟩ := ε.symm.surjective k
    cases k <;> simp⟩

theorem glue_dot {R : Type} [CommRing R] [Fintype κ] [Fintype κ₀] [Fintype κ₁] (a a' : κ₀ → R) (b b' : κ₁ → R) :
    glue ε a b ⬝ᵥ glue ε a' b' = a ⬝ᵥ a' + b ⬝ᵥ b' := by
  rw [← sumElim_dotProduct_sumElim]
  exact Equiv.sum_comp ε fun k => Sum.elim a b k * Sum.elim a' b' k

theorem continuous_glue {R X : Type} [TopologicalSpace R] [TopologicalSpace X] {a : X → κ₀ → R} {b : X → κ₁ → R}
    (ha : Continuous a) (hb : Continuous b) : Continuous fun x => glue ε (a x) (b x) := by
  refine continuous_pi fun k => ?_
  unfold glue
  cases ε k
  · exact (continuous_apply _).comp ha
  · exact (continuous_apply _).comp hb

theorem slice_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] (a : κ₀ → R) {g : (κ → R) → ℂ} (hg : g ∈ SB (κ → R)) :
    (fun b => g (glue ε a b)) ∈ SB (κ₁ → R) := by
  have hs : Continuous fun b => glue ε a b := continuous_glue ε continuous_const continuous_id
  have hinv : Function.LeftInverse (fun (x : κ → R) k => x (ε.symm (.inr k))) fun b => glue ε a b :=
    fun b => funext fun k => glue_inr ε a b k
  exact ⟨hg.1.comp_continuous hs, hg.2.comp_isClosedEmbedding (hinv.isClosedEmbedding (by fun_prop) hs)⟩

def box {R : Type} (Λ : Set (κ₀ → R)) (φ : (κ₁ → R) → ℂ) : (κ → R) → ℂ :=
  fun x => Λ.indicator 1 (fun k => x (ε.symm (.inl k))) * φ fun k => x (ε.symm (.inr k))

theorem box_glue {R : Type} (Λ : Set (κ₀ → R)) (φ : (κ₁ → R) → ℂ) (a : κ₀ → R) (b : κ₁ → R) :
    box ε Λ φ (glue ε a b) = Λ.indicator 1 a * φ b := by
  simp [box]

theorem box_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {Λ : Set (κ₀ → R)} (ho : IsOpen Λ) (hc : IsCompact Λ)
    {φ : (κ₁ → R) → ℂ} (hφ : φ ∈ SB (κ₁ → R)) : box ε Λ φ ∈ SB (κ → R) := by
  have h1 : IsLocallyConstant (Λ.indicator (1 : (κ₀ → R) → ℂ)) :=
    (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (⟨hc.isClosed, ho⟩ : IsClopen Λ)).isLocallyConstant
  refine ⟨(h1.comp_continuous (f := fun (x : κ → R) k => x (ε.symm (.inl k))) (by fun_prop)).mul
    (hφ.1.comp_continuous (f := fun (x : κ → R) k => x (ε.symm (.inr k))) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((hc.prod hφ.2.isCompact).image
    (continuous_glue ε continuous_fst continuous_snd)) fun x hx => ?_
  obtain ⟨a, b, rfl⟩ := exists_glue ε x
  rw [box_glue]
  by_cases ha : a ∈ Λ
  · rw [image_eq_zero_of_notMem_tsupport (f := φ) fun hb => hx ⟨(a, b), ⟨ha, hb⟩, rfl⟩, mul_zero]
  · rw [Set.indicator_of_notMem ha, zero_mul]

variable [Fintype κ] [Fintype κ₁]

theorem exists_slice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : κ₀ → V) :
    ∃ T : SchwartzMap (κ → V) ℂ →L[ℂ] SchwartzMap (κ₁ → V) ℂ, ∀ f b, T f b = f (glue ε a b) := by
  let L : (κ₁ → V) →L[ℝ] (κ → V) :=
    { toFun := fun b => glue ε 0 b
      map_add' := fun b b' => by rw [glue_add, add_zero]
      map_smul' := fun c b => by rw [glue_smul, smul_zero]; rfl
      cont := continuous_glue ε continuous_const continuous_id }
  have e : (fun b => glue ε a b) = fun b => glue ε a 0 + L b := funext fun b => by
    show _ = _ + glue ε 0 b
    rw [glue_add, add_zero, zero_add]
  have ht : Function.HasTemperateGrowth fun b => glue ε a b := by
    rw [e]; exact (Function.HasTemperateGrowth.const _).add L.hasTemperateGrowth
  have hl : AntilipschitzWith 1 fun b => glue ε a b := AntilipschitzWith.of_le_mul_dist fun b b' => by
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
    intro k
    simpa using dist_le_pi_dist (glue ε a b) (glue ε a b') (ε.symm (.inr k))
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ ht hl, fun f b => rfl⟩

variable {F : Type} [Field F] [NumberField F]

theorem slice_mem_schA (a : κ₀ → AF F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (fun b => Φ (glue ε a b)) ∈ schA F κ₁ := by
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    obtain ⟨T, hT⟩ := exists_slice ε fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1
    refine Submodule.subset_span ⟨T f, _, slice_mem_SB ε (fun k => (a k).2) hg, funext fun b => ?_⟩
    simp only [pureA, hT]
    rw [glue_map ε (fun z : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F z.1), glue_map ε (fun z : AF F => z.2)]
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {κ₀ : Type} [Fintype κ₀]
  (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n₁ × Fin d₁)

theorem exists_isVac {B : Base F E} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (Ma : Model σ X W) (M₁ : Model σ X₁ W₁)
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      Ma.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (p q : Matrix (Fin n) (Fin d) (AE F E) → κ₀ → AF F) (π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d₁) (AE F E))
    (hco : ∀ z, Ma.co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)) (v : Pl (F := F))
    (hlat : ∀ γ ∈ latAtV X W v, π γ ∈ latAtV X₁ W₁ v)
    (hpq : ∀ γ ∈ latAtV X W v, ∀ γ' ∈ latAtV X W v, B.ψ (p γ' ⬝ᵥ q γ) = 1)
    (hθ : ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * (p γ ⬝ᵥ q γ)) *
          B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W₁.J) (π γ) (π γ)))
    {φ : (Fin n₁ × Fin d₁ → Fv F v) → ℂ} (hφ : M₁.IsVac B.ψ v φ) :
    ∃ φa, Ma.IsVac B.ψ v φa ∧ ∀ b, φa (glue ε 0 b) = φ b := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LatOpenCpt.main σ B X W r s r' s' hX hW Ma hrat v
  set K := (latAtV X W v).map (GlobalTheory.LatVac.locCo Ma.co v) with hK
  let pr : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) →+ (κ₀ → Fv F v) :=
    { toFun := fun w k => w.1 (ε.symm (.inl k)), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hΛc : IsCompact (K.map pr : Set (κ₀ → Fv F v)) :=
    hKc.image (show Continuous fun (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) k => w.1 (ε.symm (.inl k)) by
      fun_prop)
  have hΛo : IsOpen (K.map pr : Set (κ₀ → Fv F v)) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hc : Continuous fun a : κ₀ → Fv F v => ((glue ε a 0, 0) : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) :=
      (continuous_glue ε continuous_id continuous_const).prodMk continuous_const
    refine Filter.mem_of_superset ((hKo.preimage hc).mem_nhds ?_) fun a ha => ⟨_, ha, funext fun k => glue_inl ε a 0 k⟩
    show (glue ε 0 0, 0) ∈ K
    rw [glue_zero]
    exact K.zero_mem
  have hmem : ∀ a, a ∈ K.map pr ↔ ∃ γ ∈ latAtV X W v, (fun k => evFin F v (p γ k)) = a := fun a => by
    have : ∀ γ, pr (GlobalTheory.LatVac.locCo Ma.co v γ) = fun k => evFin F v (p γ k) := fun γ => funext fun k => by
      show evFin F v ((Ma.co.e γ).1 _) = _
      simp only [hco, glue_inl]
    simp only [hK, AddSubgroup.map_map, AddSubgroup.mem_map, AddMonoidHom.comp_apply, this]
  set Λ := K.map pr
  have h0 : ∀ b, box ε (Λ : Set _) φ (glue ε 0 b) = φ b := fun b => by
    rw [box_glue, Set.indicator_of_mem Λ.zero_mem, Pi.one_apply, one_mul]
  obtain ⟨hSB, hne, θ, hθ1, hA⟩ := hφ
  refine ⟨box ε Λ φ, ⟨box_mem_SB ε hΛo hΛc hSB, fun h => hne (funext fun b => by rw [← h0, h]; rfl), θ, hθ1,
    fun γ hγ R hR => ?_⟩, h0⟩
  have hat : ∀ u, evFin F v u = 0 → u • p γ = 0 ∧ u • q γ = 0 := fun u hu => by
    have h1 := congrArg Ma.co.e ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ u hu)
    rw [map_smul, map_zero, hco] at h1
    exact ⟨funext fun k => by simpa using congrFun (congrArg Prod.fst h1) (ε.symm (.inl k)),
      funext fun k => by simpa using congrFun (congrArg Prod.snd h1) (ε.symm (.inl k))⟩
  funext x
  obtain ⟨a, b, rfl⟩ := exists_glue ε x
  have hp : (fun k => evFin F v (p γ k)) ∈ Λ := (hmem _).2 ⟨γ, hγ, rfl⟩
  simp only [Darboux.rho, schr, tens, hco, glue_dot, glue_add, glue_map ε (evFin F v), Pi.smul_apply, box_glue]
  by_cases ha : (fun k => evFin F v (a k)) ∈ Λ
  · have ha' : (fun k => evFin F v ((a + p γ) k)) ∈ Λ := by
      simp only [Pi.add_apply, map_add (f := _)]
      exact Λ.add_mem ha hp
    have hR₁ : Rest (evFin F v) φ fun b => R (glue ε a b) := by
      refine ⟨fun x z hz => ?_, ?_⟩
      · have := hR.1 (glue ε a x) (glue ε 0 z) fun u hu => by rw [glue_smul, hz u hu, smul_zero, glue_zero]
        rwa [glue_add, add_zero] at this
      · have := slice_mem_schA ε a hR.2
        simp only [tens, glue_map ε (evFin F v), box_glue, Set.indicator_of_mem ha, Pi.one_apply, one_mul] at this
        exact this
    have key := congrFun (hA (π γ) (hlat γ hγ) _ hR₁) b
    simp only [Darboux.rho, schr, tens, Pi.smul_apply] at key
    have hs : ∀ c, R (glue ε (a + p γ) c) = R (glue ε a c) := fun c => by
      have := hR.1 (glue ε a c) (glue ε (p γ) 0) fun u hu => by rw [glue_smul, (hat u hu).1, smul_zero, glue_zero]
      rwa [glue_add, add_zero] at this
    have h1 : B.ψ (a ⬝ᵥ q γ) = 1 := by
      obtain ⟨γ', hγ', e⟩ := (hmem _).1 ha
      rw [← hpq γ hγ γ' hγ']
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      have := congrFun (hat (a k - p γ' k) (by rw [map_sub, sub_eq_zero]; exact (congrFun e k).symm)).2 k
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      linear_combination this
    rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha', hs, hθ θ hθ1 γ hγ, mul_add, add_add_add_comm,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul B.ψ (a ⬝ᵥ q γ), h1]
    simp only [Pi.one_apply, one_mul, smul_eq_mul] at key ⊢
    rw [mul_assoc, key]
    ring
  · have ha' : (fun k => evFin F v ((a + p γ) k)) ∉ Λ := fun h => ha (by
      have := Λ.sub_mem h hp
      convert this using 1
      funext k
      simp)
    rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha']
    simp

theorem conj_conj {B : Base F E} (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])

theorem cA_cA {B : Base F E} (hB : B.IsGood σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, conj_conj hB]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {α β α' β' : Type} [Fintype α] [Fintype β]
  [Fintype α'] [Fintype β']

theorem hTens_eq_trace (J : Matrix α α S) (J' : Matrix β β S) (z z' : Matrix α β S) :
    hTens c J J' z z' = (zᵀ * J * z'.map c * J'ᵀ).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

theorem hTens_mul (J : Matrix α α S) (J' : Matrix β β S) (P : Matrix α α' S) (P' : Matrix β β' S) (z z' : Matrix α' β' S) :
    hTens c J J' (P * z * P'ᵀ) (P * z' * P'ᵀ) = hTens c (Pᵀ * J * P.map c) (P'ᵀ * J' * P'.map c) z z' := by
  have hm : (P * z' * P'ᵀ).map c = P.map c * z'.map c * (P'.map c)ᵀ := by
    rw [show (P * z' * P'ᵀ).map c = (P * z').map c * P'ᵀ.map c from Matrix.map_mul (f := c.toRingHom),
      show (P * z').map c = P.map c * z'.map c from Matrix.map_mul (f := c.toRingHom)]
    rfl
  rw [hTens_eq_trace, hTens_eq_trace, hm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem conj_pair (hc : ∀ z, c (c z) = z) {J : Matrix α α S} {η : S} (hJ : ∀ i j, c (J j i) = η * J i j) (u w : α → S) :
    c (∑ i, ∑ k, u i * J i k * c (w k)) = η * ∑ i, ∑ k, w i * J i k * c (u k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

end Alg

section Plane

variable {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {B : Base F E} {H : Plane E m m₁}

def frame (H : Plane E m m₁) : Matrix (Fin m) (Fin m₁ ⊕ Fin 2) E := Matrix.fromCols H.ι (Matrix.of fun i => ![H.x i, H.y i])

omit [NumberField F] [Algebra F E] in
theorem frame_mulVec (H : Plane E m m₁) (w : Fin m₁ ⊕ Fin 2 → E) :
    frame H *ᵥ w = w (.inr 0) • H.x + H.ι *ᵥ (fun i => w (.inl i)) + w (.inr 1) • H.y := by
  funext i
  simp [frame, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem exists_frame_inv (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsFullLattice E) :
    ∃ Q : Matrix (Fin m₁ ⊕ Fin 2) (Fin m) E, frame H * Q = 1 ∧ Q * frame H = 1 ∧ ∀ u ∈ Y.L,
      (fun i => (Q *ᵥ u) (.inl i)) ∈ Y₁.L ∧ (Q *ᵥ u) (.inr 0) • H.x ∈ Y.L ∧ (Q *ᵥ u) (.inr 1) • H.y ∈ Y.L := by
  have h1 : ∀ z ∈ Y.L, ∃ w, frame H *ᵥ w = z ∧ (fun i => w (.inl i)) ∈ Y₁.L ∧ w (.inr 0) • H.x ∈ Y.L ∧
      w (.inr 1) • H.y ∈ Y.L := fun z hz => by
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hH.split z hz
    exact ⟨Sum.elim u ![s, t], frame_mulVec H _, hu, hs, ht⟩
  have h2 : LinearMap.range (frame H).mulVecLin = ⊤ := by
    apply top_unique
    rw [← hL.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨w, hw, -⟩ := h1 z hz
    exact ⟨w, hw⟩
  choose f hf using fun j : Fin m => LinearMap.range_eq_top.1 h2 (Pi.single j 1)
  have h3 : frame H * (Matrix.of f)ᵀ = 1 := by
    ext i j
    rw [Matrix.one_apply, ← Pi.single_apply j (1 : E) i, ← hf j]
    rfl
  have h4 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hH.rank])).1 h3
  refine ⟨_, h3, h4, fun u hu => ?_⟩
  obtain ⟨w, rfl, hw⟩ := h1 u hu
  rwa [Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]

theorem frame_gram (hB : B.IsGood σ) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {η : E} (hη : η * η = 1)
    (hJ : ∀ i j, σ (Y.J j i) = η * Y.J i j) :
    (frame H)ᵀ * Y.J * (frame H).map σ = Matrix.fromBlocks Y₁.J 0 0 !![0, 1; η, 0] := by
  have hf : ∀ u w, form σ Y.J u w = ∑ i, ∑ k, u i * Y.J i k * σ (w k) := fun u w => by
    simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hs : ∀ u w, form σ Y.J w u = η * σ (form σ Y.J u w) := fun u w => by
    rw [hf u w, conj_pair σ (conj_conj hB) hJ, ← mul_assoc, hη, one_mul, hf]
  have he : ∀ a b, ((frame H)ᵀ * Y.J * (frame H).map σ) a b = form σ Y.J (fun i => frame H i a) fun i => frame H i b :=
    fun a b => by
      simp only [hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
      exact Finset.sum_comm
  have hi : ∀ j, (fun i => frame H i (.inl j)) = H.ι *ᵥ Pi.single j 1 := fun j => by
    funext i; simp [frame]
  have hx : (fun i => frame H i (.inr 0)) = H.x := rfl
  have hy : (fun i => frame H i (.inr 1)) = H.y := rfl
  ext (a | a) (b | b)
  · rw [Matrix.fromBlocks_apply₁₁, ← hH.gram]; rfl
  · rw [he, hi]
    fin_cases b
    · exact (hH.orth _).1
    · exact (hH.orth _).2
  · rw [he, hi, hs]
    fin_cases a
    · exact (congrArg (fun t => η * σ t) (hH.orth _).1).trans (by simp)
    · exact (congrArg (fun t => η * σ t) (hH.orth _).2).trans (by simp)
  · rw [he]
    fin_cases a <;> fin_cases b
    · exact hH.xx
    · exact hH.xy
    · exact (hs H.x H.y).trans (by simp [hH.xy])
    · exact hH.yy

def mask (S : Type) [CommRing S] (m₁ : ℕ) (c s t : ℤ) : Matrix (Fin m₁ ⊕ Fin 2) (Fin m₁ ⊕ Fin 2) S :=
  Matrix.diagonal (Sum.elim (fun _ => (c : S)) ![(s : S), (t : S)])

end Plane

theorem incM_mul {α β γ : Type} [Fintype β] (A : Matrix α β E) (C : Matrix β γ E) : incM F (A * C) = incM F A * incM F C :=
  Matrix.map_mul

theorem lat_map {A : Matrix (Fin n₁) (Fin n) E} {A' : Matrix (Fin d₁) (Fin d) E} (hA : ∀ u ∈ X.L, A *ᵥ u ∈ X₁.L)
    (hA' : ∀ u ∈ W.L, A' *ᵥ u ∈ W₁.L) {v : Pl (F := F)} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    incM F A * γ * (incM F A')ᵀ ∈ latAtV X₁ W₁ v := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hav, _, hA x hx, _, hA' y hy, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, ← incM_mul, show (incM F A')ᵀ = incM F A'ᵀ from rfl, ← incM_mul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem hx

end GlobalTheory.ThK.Adapt

end
