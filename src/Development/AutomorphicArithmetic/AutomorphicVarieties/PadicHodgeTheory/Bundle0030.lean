module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SnocZeroLastCoordinateLast
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrystallineTransferSurjection
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem crystalline_transfer_surjection {l : ℕ} [Fact l.Prime] {G G' A A' V V' : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [CommRing A']
    [Algebra ℚ_[l] A'] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V']
    (φ : G →* GQ l) (e : G' →* G) (he : Function.Surjective e) (ρ : Representation A G V)
    (ρ' : Representation A' G' V') (f : V ≃ₗ[ℚ_[l]] V') (hf : ∀ g x, f (ρ (e g) x) = ρ' g (f x)) :
    IsCr φ ρ ↔ IsCr (φ.comp e) ρ' := by
  have hr : (φ.comp e).range = φ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 he, ← MonoidHom.range_eq_map]
  let F : V ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hF : ∀ g x, F (actC φ (resCoef ℚ_[l] ρ) (e g) x) = actC (φ.comp e) (resCoef ℚ_[l] ρ') g (F x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] ρ)).map F.toLinearMap = Dcr (φ.comp e) (resCoef ℚ_[l] ρ') := by
    ext x
    obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      ← hF, F.injective.eq_iff]
    exact he.forall
  unfold IsCr
  rw [hr, ← hD, LinearEquiv.finrank_map_eq, f.finrank_eq]

private theorem crystalline_iff_on_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    (φ : G →* GQ l) (ρ : Representation A G V) : IsCr φ ρ ↔ CrOn φ ρ ⊤ :=
  crystalline_transfer_surjection φ (⊤ : Subgroup G).subtype (fun g => ⟨⟨g, trivial⟩, rfl⟩) ρ _ (LinearEquiv.refl _ _)
    fun _ _ => rfl

private theorem crystalline_conj_invariant {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}
    (φ : G →* GQ l) (r : G →* GL (Fin n) A) (h : GL (Fin n) A) :
    IsCr φ (colRep r) ↔ IsCr φ (colRep (conjGL h r)) := by
  have := crystalline_transfer_surjection φ (MonoidHom.id G) Function.surjective_id (colRep r) (colRep (conjGL h r))
    ((Matrix.toLinearEquiv' (h : Matrix (Fin n) (Fin n) A) h.invertible).restrictScalars ℚ_[l]) fun g x => by
      simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]
  simpa using this

private theorem continuous_dual_number_qcont {l : ℕ} [Fact l.Prime] {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] (f : X → DualNumber E) (hf : Continuous f) : QCont l f := by
  have h1 : Continuous fun x => (f x).fst := TrivSqZeroExt.continuous_fst.comp hf
  have h2 : Continuous fun x => (f x).snd := TrivSqZeroExt.continuous_snd.comp hf
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  unfold QCont
  clear hf
  letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] (DualNumber E)
  rw [e]
  exact ((IsModuleTopology.continuous_of_linearMap _).comp h1).add
    ((IsModuleTopology.continuous_of_linearMap _).comp h2)

private theorem open_subgroup_finite_index {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (H : Subgroup G) (hH : IsOpen (H : Set G)) : H.FiniteIndex := by
  have hc : IsClosed (φ.range : Set (GQ l)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
  haveI : CompactSpace G := (IsClosedEmbedding.mk hφ.isEmbedding hc).compactSpace
  haveI := H.quotient_finite_of_isOpen hH
  exact Subgroup.finiteIndex_of_finite_quotient

theorem UpperTheory.V.Loc.pr6 :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] {Y : Type} [AddCommGroup Y] [Module E Y] [Module ℚ_[l] Y] [IsScalarTower ℚ_[l] E Y] [FiniteDimensional ℚ_[l] Y] [TopologicalSpace Y] [IsModuleTopology ℚ_[l] Y] [IsTopologicalAddGroup Y] [ContinuousConstSMul E Y] (ρ : Representation E G Y), ContAction ρ → ∀ y ∈ Z1 ρ, ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → ∀ {n : ℕ} (r : H →* GL (Fin n) E), Continuous (fun g => (r g : Matrix (Fin n) (Fin n) E)) → ∀ (ι : Y →ₗ[E] Matrix (Fin n) (Fin n) E) (p : Matrix (Fin n) (Fin n) E →ₗ[E] Y), (∀ x, p (ι x) = x) → (∀ (g : H) x, ι (ρ g x) = adGL r g (ι x)) → (∀ (g : H) X, p (adGL r g X) = ρ g (p X)) → ∀ r' : H →* GL (Fin n) (DualNumber E), (∀ (g : H) i j, (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j = ⟨(r g : Matrix (Fin n) (Fin n) E) i j, (ι (y g) * (r g : Matrix (Fin n) (Fin n) E)) i j⟩) → ∀ (h : GL (Fin n) (DualNumber E)) (κ : Fin n → H →* (DualNumber E)ˣ) (w : Fin n → ℤ), UpperTri (conjGL h r') κ → StrictAnti w → (∀ i (g : H), φ g ∈ Iq l → κ i g = cycA l l (DualNumber E) (φ g) ^ w i) → (∀ i j, i < j → ∃ g : H, (κ i g : DualNumber E).fst ≠ (κ j g : DualNumber E).fst * (cycA l l E (φ g) : E)) → IsCr (φ.comp H.subtype) (colRep r) ∧ IsCr (φ.comp H.subtype) (colRep r') ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro P l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ _ ρ hρ y hy H _ hH n r hr ι p hp hι hpe r' hr' h κ w
    hU hw hκ hne
  haveI := open_subgroup_finite_index φ hφ H hH
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hyc : Continuous fun g : H => ι (y g) :=
    (IsModuleTopology.continuous_of_linearMap (ι.restrictScalars ℚ_[l])).comp (hy.1.comp continuous_subtype_val)
  have hy' : (fun g : H => ι (y g)) ∈ Z1 (adGL r) := ⟨hyc, fun g k => by
    simp only []
    rw [Subgroup.coe_mul, hy.2, map_add (f := _), hι]⟩
  have hr'c : Continuous fun g => (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) := by
    refine continuous_matrix fun i j => ?_
    simp only [hr']
    exact Continuous.prodMk (hr.matrix_elem i j) ((hyc.matrix_mul hr).matrix_elem i j)
  have hcc : ∀ i j, QCont l fun g => (conjGL h r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j := fun i j =>
    continuous_dual_number_qcont _ (((continuous_const.matrix_mul hr'c).matrix_mul continuous_const).matrix_elem i j)
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  have h1 : IsCr (φ.comp H.subtype) (colRep r') :=
    (crystalline_conj_invariant _ r' h).2 (prC P _ hφH (TrivSqZeroExt.fstHom E E E)
      (fun a ha => ⟨2, by ext <;> simp_all [pow_two]⟩) (conjGL h r') hcc κ w hU hw hκ hne)
  obtain ⟨h2, h3⟩ := (deformCr _ hφH r hr _ hy' r' hr' ⊤ (by simp)).1 ((crystalline_iff_on_top _ _).1 h1)
  refine ⟨(crystalline_iff_on_top _ _).2 h2, h1, (z1fDesc φ ρ H y hy).2 ?_⟩
  have := (z1fMap (φ.comp H.subtype) (adGL r) (ρ.comp H.subtype : Representation E H Y)).2
    (p.restrictScalars ℚ_[l]) hpe _ h3
  simpa [hp] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFrobeniusFixedPeriod
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_trace {k U D : Type} [Field k] [Field U] [AddCommGroup D] [Module k D]
    (m : U →+* End k D) (φ : End k D) (n : ℕ) (hn : 0 < n) (t : ℕ → U)
    (ht : ∀ i j : Fin n, t i = t j → i = j) (htn : t n = t 0)
    (hφ : ∀ i j : ℕ, φ ^ i * m (t 0 ^ j) = m (t i ^ j) * φ ^ i) (x : D) (hx : x ≠ 0) (hp : (φ ^ n) x = x) :
    ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 ∧
      φ ((∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x) = (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x := by
  have h1 : ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 := by
    by_contra hc
    push Not at hc
    letI : Module U D := Module.compHom D m
    refine hx ((Module.forall_dual_apply_eq_zero_iff U x).mp fun f => ?_)
    have h2 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := fun i : Fin n => t i)
      (v := fun i : Fin n => f ((φ ^ (i : ℕ)) x)) ht (fun j => by
        have h3 := congrArg f (hc j)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_zero, LinearMap.sum_apply, map_sum, Finset.sum_range] at h3
        rw [← h3]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hφ, mul_comm, ← smul_eq_mul, ← map_smul]
        rfl)
    simpa using congrFun h2 ⟨0, hn⟩
  obtain ⟨j, hj⟩ := h1
  refine ⟨j, hj, ?_⟩
  have h4 : (φ ^ n * m (t 0 ^ j)) x = (φ ^ 0 * m (t 0 ^ j)) x := by
    rw [hφ, htn, End.mul_apply, hp, pow_zero, one_mul]
  have h5 := Finset.sum_range_succ (fun i => (φ ^ i * m (t 0 ^ j)) x) n
  rw [Finset.sum_range_succ', h4, add_left_inj] at h5
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum, ← h5]
  conv_rhs => rw [h5, ← h5]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ', mul_assoc, End.mul_apply φ]

private theorem exists_orbit (l : ℕ) [hl : Fact l.Prime] (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ↥(MaximalUnramifiedExtension l), (frobUr l ^ n) c = c ∧
      ∀ i j : Fin n, (frobUr l ^ (i : ℕ)) c = (frobUr l ^ (j : ℕ)) c → i = j := by
  have h2 := hl.out.two_le
  have hlt : ∀ i, i < n → l ^ i < l ^ n - 1 := by
    intro i hi
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    have h3 : l ^ i ≤ l ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 1 < l ^ r := Nat.one_lt_pow (by omega) (by omega)
    have h5 : l ^ r * 2 ≤ l ^ r * l := Nat.mul_le_mul_left _ h2
    rw [pow_succ]; omega
  have h0 : 0 < l ^ n - 1 := lt_of_le_of_lt (Nat.zero_le _) (hlt 0 (by omega))
  have hd : ¬ l ∣ l ^ n - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ n - 1) := ⟨h0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, h0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ n - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun i j hij => ?_⟩
  · rw [frobUr_pow_root _ _ _ h0 hd h1, show l ^ n = (l ^ n - 1) + 1 by omega, pow_succ, h1, one_mul]
  · rw [frobUr_pow_root _ _ _ h0 hd h1, frobUr_pow_root _ _ _ h0 hd h1] at hij
    have h6 : z ^ l ^ (i : ℕ) = z ^ l ^ (j : ℕ) := congrArg Subtype.val hij
    exact Fin.ext (Nat.pow_right_injective h2 (hz.pow_inj (hlt _ i.2) (hlt _ j.2) h6))

private theorem zpow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (y : D)
    (hy : (u : End k D) y = y) (n : ℤ) : ((u ^ n : (End k D)ˣ) : End k D) y = y :=
  (GlobalTheory.PstLaws.vecStab (Units.coeHom (End k D)) y).zpow_mem hy n

private theorem pow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (a : End k D) (y : D)
    (n : ℕ) (hc : Commute a ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) (ha : a y = y)
    (hy : (a * ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) y = y) : ((u : End k D) ^ n) y = y := by
  rwa [hc.eq, End.mul_apply, ha, zpow_natCast, Units.val_pow_eq_pow_val] at hy

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
  [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
  (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem exists_stab {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (y : ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → g ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) y := by
  obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
  exact ⟨K', fun g hg => Subtype.ext (hK' g hg)⟩

private theorem deg_frob_inv_pow (s : ℕ) : deg ((frob h)⁻¹ ^ s) = -(s : ℤ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := deg_mul ((frob h)⁻¹ ^ (s + 1)) (frob h)
    rw [pow_succ, inv_mul_cancel_right, ih, deg_frob] at h1
    rw [pow_succ]; push_cast; omega

variable (ρ : Representation LL ↥(GK Bw.Kw) V)

private theorem fix_of_weil (z : ↥(Dpst P ρ)) (hz : ∀ σ, actD P ρ (weilToGK Bw h σ) z = z)
    (g : ↥(GK Bw.Kw)) : actD P ρ g z = z := by
  obtain ⟨K', hK'⟩ := exists_stab P ρ z
  haveI := K'.2
  let S := (GlobalTheory.PstLaws.vecStab (actD P ρ) z).comap Bw.e.toMonoidHom
  have hS : IsOpen (S : Set ↥(Dec (F := F) A)) := by
    refine Subgroup.isOpen_mono (H₁ := ((GK K').subgroupOf (GK Bw.Kw)).comap Bw.e.toMonoidHom)
      (fun τ hτ => hK' _ hτ) ?_
    exact (IntermediateField.fixingSubgroup_isOpen K'.1).preimage (continuous_subtype_val.comp Bw.e_cont)
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  obtain ⟨τ, rfl⟩ := Bw.e.surjective g
  exact hd.induction_on (p := fun τ => τ ∈ S) τ (S.isClosed_of_isOpen hS) hz

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

include hj in
private theorem exists_period (x : ↥(Dpst P ρ)) (hx : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ n : ℕ, 2 ≤ n ∧ (phiD P ρ ^ n) x = x := by
  have hf : resDeg l w ≠ 0 := by
    intro h0
    have hq1 := GlobalTheory.WeilDeligne.one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  obtain ⟨K', hK'⟩ := exists_stab P ρ x
  haveI := GlobalTheory.PstLaws.finite_quotient K' _ hK'
  haveI : (GlobalTheory.PstLaws.vecStab (actD P ρ) x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨r, hr0, -, hr⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := GlobalTheory.PstLaws.vecStab (actD P ρ) x)) (weilToGK Bw h (frob h)⁻¹)
  have hr2 : weilToGK Bw h ((frob h)⁻¹ ^ (r * 2)) ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) x := by
    rw [map_pow (weilToGK Bw h), pow_mul]
    exact (GlobalTheory.PstLaws.vecStab (actD P ρ) x).pow_mem hr 2
  have h2 := hx ((frob h)⁻¹ ^ (r * 2))
  have e : -alpha l ((frob h)⁻¹ ^ (r * 2)) = ((resDeg l w * (r * 2) : ℕ) : ℤ) := by
    rw [alpha, deg_frob_inv_pow]; push_cast; ring
  rw [weilD_apply, e] at h2
  refine ⟨_, ?_, pow_fix (phiU P ρ) _ x _ (commute_actD_phiU P ρ _ _) hr2 h2⟩
  have : 0 < resDeg l w * r := Nat.mul_pos (Nat.pos_of_ne_zero hf) hr0
  rw [← mul_assoc]; omega

include hj in
private theorem existsFrobeniusFixedPeriod (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (hxI : ∀ s, weilD Bw h P ρ (ineIncl h s) x = x)
    (hW : ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  obtain ⟨n, hn, hp⟩ := exists_period h Bw hj P ρ x (hW x hxI)
  obtain ⟨c, hc1, hc2⟩ := exists_orbit l n hn
  obtain ⟨j, hz0, hz1⟩ := exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2
    (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp
  refine ⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩
  refine (congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans
    (hW _ (fun s => ?_) σ)
  have hcm : Commute (weilD Bw h P ρ (ineIncl h s)) (∑ i ∈ Finset.range n, phiD P ρ ^ i *
      mulD P ρ ((frobUr l ^ 0) c ^ j)) := by
    refine Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i)
      (weilD_mulD Bw h P ρ hj _ _)
    rw [weilD_ineIncl]
    exact (phiD_actD P ρ _).symm
  exact (LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hxI s))

end

theorem UpperTheory.exists_frobenius_fixed_period :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (_hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → (∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x) → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  intro F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hxI⟩ hW
  exact existsFrobeniusFixedPeriod h Bw hj P ρ x hx0 hxI hW
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem finite_emb {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) :
    Finite (Emb l w) := by
  refine Finite.of_injective
    (fun j : Emb l w => (j.1.comp (algebraMap F (w.adicCompletion F)) : F →+* Qbar l)) fun j j' hjj => ?_
  refine Subtype.ext (DFunLike.coe_injective ?_)
  refine (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w)).equalizer j.2 j'.2 ?_
  funext x
  exact DFunLike.congr_fun hjj x

private theorem wt_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)
    (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ)
    (ho : IsOpen (ph.ker : Set ↥(Ine (F := F) A)))
    (H : ∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) :
    IsWtPart h κ 0 ph :=
  ⟨ho, fun a _ σ => by rw [H]; simp⟩

private theorem wt_mul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt wt' : Emb l w → ℤ} {ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (H' : IsWtPart h κ' wt' ph') : IsWtPart h (κ * κ') (wt + wt') (ph * ph') := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker ⊓ ph'.ker) (fun x hx => ?_) (H.1.inter H'.1)
    have h1 : ph x = 1 := hx.1
    have h2 : ph' x = 1 := hx.2
    simp [MonoidHom.mem_ker, h1, h2]
  · have h1 := H.2 a ha σ
    have h2 := H'.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 h2 ⊢
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_mul_mul_comm, Units.val_mul, h1, h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ ((map_ne_zero τ.1).2 (Units.ne_zero _))]

private theorem wt_zpow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt : Emb l w → ℤ} {ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (m : ℤ) : IsWtPart h (κ ^ m) (m • wt) (ph ^ m) := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker) (fun x hx => ?_) H.1
    have h1 : ph x = 1 := hx
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, h1, one_zpow]
  · have h1 := H.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 ⊢
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, ← mul_zpow, Units.val_zpow_eq_zpow_val, h1, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, neg_mul, mul_comm]

theorem UpperTheory.V.Loc.laMul :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), (∀ (κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt wt' : Emb l w → ℤ) (ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsWtPart h κ wt ph → IsWtPart h κ' wt' ph' → IsWtPart h (κ * κ') (wt + wt') (ph * ph') ∧ IsWtPart h κ⁻¹ (-wt) ph⁻¹) ∧ (∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt : Emb l w → ℤ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ) (m : ℤ), IsWtPart h κ wt ph → IsWtPart h (κ ^ m) (m • wt) (ph ^ m)) ∧ ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsOpen (ph.ker : Set ↥(Ine (F := F) A)) → (∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) → IsWtPart h κ 0 ph := by
  intro F Ω _ _ _ _ _ l _ A w h
  refine ⟨fun κ κ' wt wt' ph ph' H H' => ⟨wt_mul H H', ?_⟩, fun κ wt ph m H => wt_zpow H m, wt_one h⟩
  simpa only [zpow_neg_one, neg_smul, one_smul] using wt_zpow H (-1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtin
section
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isSmoothChar_of_comp' {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (hs : Function.Surjective a)
    (hc : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ))
    (ho : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : WeilDeligne.IsSmooth (χ.comp a)) : IsSmoothChar χ := by
  haveI : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have hK : IsOpen {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1} := hχ
  have hC : IsClosed ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ) :=
    (hK.isClosed_compl.isCompact.image hc).isClosed
  have hU : {x : (w.adicCompletion E)ˣ | valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1} ∈ nhds 1 := by
    have h1 : {x : w.adicCompletion E | valuation (w.adicCompletion E) (x - 1) < 1} ∈ nhds 1 := by
      rw [IsValuativeTopology.mem_nhds_iff]
      exact ⟨1, fun z hz => by simpa [neg_add_eq_sub] using hz⟩
    have h2 := Units.continuous_val.continuousAt (x := (1 : (w.adicCompletion E)ˣ)) h1
    refine Filter.mem_of_superset h2 fun x hx => ?_
    have h3 : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - 1) < 1 := hx
    have := Valuation.map_one_add_of_lt _ h3
    simpa using this
  refine Subgroup.isOpen_of_mem_nhds χ.ker (g := 1) ?_
  have h1 : (1 : (w.adicCompletion E)ˣ) ∈ ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ)ᶜ := by
    rintro ⟨σ, hσ, e⟩
    refine hσ ?_
    have e' : a (ineIncl h σ) = 1 := e
    simp [e']
  refine Filter.mem_of_superset (Filter.inter_mem hU (hC.isOpen_compl.mem_nhds h1)) ?_
  rintro x ⟨hx, hx'⟩
  obtain ⟨σ, rfl⟩ := hs x
  have h0 : deg σ = 0 := by
    have := ho σ
    rw [ord_eq_zero_iff.2 hx] at this
    omega
  by_contra hn
  exact hx' ⟨⟨σ, deg_eq_zero_iff.mp h0⟩, hn, rfl⟩

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

theorem UpperTheory.V.Loc.laArtin :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ∃ a, IsLocalArtin h a := by
  intro hG E Ω _ _ _ _ _ A w h
  obtain ⟨art, hart⟩ := hG E Ω
  obtain ⟨a, hs, ho, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin E Ω A w h art hart
  have hc := GlobalTheory.ArtinInvCont.continuous_inv_on_ine E Ω A w h art a hart ho hg
  refine ⟨a, hs, hc, ho, fun ξ hξ => ?_, fun art' hart' => ?_⟩
  · have hker : a.ker ≤ ξ.ker := fun σ hσ => by
      refine GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one E Ω A w h ξ hξ σ ?_
      rw [← hg σ, MonoidHom.mem_ker.1 hσ, map_one, map_one]
    have e : ξ = (a.liftOfSurjective hs ⟨ξ, hker⟩).comp a :=
      (MonoidHom.liftOfRightInverse_comp a _ (Function.rightInverse_surjInv hs) ⟨ξ, hker⟩).symm
    exact ⟨_, isSmoothChar_of_comp' hs hc ho (e ▸ hξ), e⟩
  · rw [GlobalTheory.ArtinUniq.globalArtin_unique E Ω art' art hart' hart]
    exact hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem UpperTheory.V.Loc.laCyc :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → IsWtPart h ((cycBar F Ω l).comp (Dec (F := F) A).subtype) (fun _ => -1) 1 := by
  intro H F Ω _ _ _ _ _ l _ A w h _
  refine ⟨by simp, fun a ha σ => ?_⟩
  obtain ⟨art, hart⟩ := H F Ω
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (CharAboveModel.absPow_isAlgPos F 1)
  have e : μ = cycBar F Ω l ^ 1 := CharAboveModel.eq_cyc_pow hart hμ hL
  rw [pow_one] at e
  subst e
  have h1 := hL.loc (a (ineIncl h σ)) _ (ha.glob art hart (ineIncl h σ))
  have hu : Formalism.L2.Host.IsUnitAt w (a (ineIncl h σ)) := by
    have h2 := ha.ord_eq (ineIncl h σ)
    rw [deg_ineIncl, neg_zero] at h2
    haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1
      (GlobalTheory.SmGL.ord_eq_zero_iff.1 h2)
  rw [(Model.absPow_isAbsPow F (1 : ℕ)).1 w _ hu] at h1
  simp only [Units.val_one, map_one, one_mul, locPow] at h1
  simpa using h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

theorem UpperTheory.V.Loc.laHecke :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (art : Neutral.B1.Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ (ι : Qbar l ≃+* ℂ) (χ : Formalism.L2.Host.HChar F) (n : (F →+* ℂ) → ℤ) (μ : G F Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → (∃ a, IsLocalArtin h a) → IsLocAlg h (μ.comp (Dec (F := F) A).subtype) fun τ => -n ((ι.toRingHom.comp τ.1).comp (algebraMap F (w.adicCompletion F))) := by
  intro F Ω _ _ _ _ _ l _ A w h art hart ι χ n μ hμ ⟨a0, ha0⟩
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  have hs : GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := GlobalTheory.HeckeComp.smooth_loc χ w
  let φ : Ine (F := F) A →* ℂˣ := ((χ.loc w).comp a0).comp (ineIncl h)
  have hφ : IsOpen (φ.ker : Set (Ine (F := F) A)) := IsOpen.preimage ha0.cont hs
  refine ⟨((Units.map ι.symm.toRingHom.toMonoidHom).comp φ)⁻¹, ?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (fun x hx => ?_) hφ
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply, hx, map_one, inv_one]
  · have e : a (ineIncl h σ) = a0 (ineIncl h σ) :=
      hinj ((ha.glob art hart _).trans (ha0.glob art hart _).symm)
    have h1 := hμ.loc (a0 (ineIncl h σ)) _ (ha0.glob art hart _)
    have h0 : ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ) ≠ 0 := (map_ne_zero ι.symm).2 (Units.ne_zero _)
    rw [e, Units.val_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    simp only [neg_neg]
    show ((μ (ineIncl h σ : Weil h) : (Qbar l)ˣ) : Qbar l) * (ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ))⁻¹ = locPow ι n w (a0 (ineIncl h σ))
    rw [h1, mul_comm, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
end

