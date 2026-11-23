module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixed
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.StableFix

theorem SemiBC.span_eq {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
    rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, rfl⟩
  exact Submodule.eq_top_iff'.2 fun y => by
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem kappa_act {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (s : GQ l) (g : G) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, TWact (galOW O s) T g (kappa T y) =
      kappa T (TensorProduct.map (galW l s).toLinearMap (actZ T g) y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem kappa_smul' {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w' x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

variable (P : PhiMod O K l e a ι)

theorem inclO_smul_mem_MA (r : OA l O) {v : ι → OW l O} (hv : v ∈ MA P) : inclO l O r • v ∈ MA P := by
  obtain ⟨c, rfl⟩ := hv
  exact ⟨r • c, funext fun i => (map_mul (inclO l O) r (c i))⟩

theorem inclO_smul_mem_LA (r : OA l O) {v : ι → OW l O} (hv : v ∈ LA t ϖ P) : inclO l O r • v ∈ LA t ϖ P := by
  obtain ⟨c, rfl⟩ := hv
  refine ⟨r • c, ?_⟩
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul (inclO l O) r (c i))

abbrev eb (i : ι) : ι → OW l O := fun j => if i = j then 1 else 0

theorem phiW_eb (i : ι) : phiW t ϖ P (eb i) = frobMat t ϖ P *ᵥ eb i := by
  rw [phiW_apply]
  congr 1
  funext j
  show frobOW l O (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> simp

theorem phiW_inclV (c : ι → OA l O) : phiW t ϖ P (inclV l O ι c) = inclL t ϖ P (fun i => frobOA l O (c i)) := by
  rw [phiW_apply, inclL_apply]
  congr 1
  funext j
  exact frobOW_inclO (c j)

def mb (i : ι) : Vec K a ι := fun _ j => if i = j then 1 else 0

theorem mb_mem (i : ι) : (mb i : Vec K a ι) ∈ P.M :=
  mem_tot.2 fun τ j => by
    change (if i = j then (1 : K⟦X⟧) else 0) ∈ A O K
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem toW_mb (i : ι) : toW t ϖ P ⟨mb i, mem_ME_of_mem_M (mb_mem P i)⟩ = eb i := by
  funext j
  rw [toW_apply]
  show _ = (if i = j then (1 : OW l O) else 0)
  split_ifs with h
  · convert map_one (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]
  · convert map_zero (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem add_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (z z' : E.M (ainfObj (ϖ.field a))) (v v' : ι → OW l O), I.j v = kappa T (j z) → I.j v' = kappa T (j z') →
      I.j (v + v') = kappa T (j (z + z')) := by
  letI := zlLat T
  intro j z z' v v' hv hw
  rw [I.j.map_add, hv, hw, j.map_add, (kappa T).map_add]

theorem smul_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (c : (ainfObj (ϖ.field a)).A) (z : E.M (ainfObj (ϖ.field a))) (v : ι → OW l O), I.j v = kappa T (j z) →
      I.j (inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfId (ϖ.field a) c) • v) = kappa T (j (c • z)) := by
  letI := zlLat T
  intro j c z v hv
  have e1 : j (c • z) = inclW l (ainfId (ϖ.field a) c) • j z := j.map_smulₛₗ c z
  rw [e1, kappa_smul', LinearEquiv.map_smul, hv, inclO_tmul]

theorem span_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
      (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (j (E.tr (ϖ.toAinf a) x))) ↔
        ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) →
      ∀ z : E.M (ainfObj (ϖ.field a)), ∃ v ∈ MA P, I.j v = kappa T (j z) := by
  letI := zlLat T
  intro j hE z
  have hz : z ∈ Submodule.span (ainfObj (ϖ.field a)).A (Set.range (E.tr (ϖ.toAinf a))) := by
    rw [SemiBC.span_eq (E.tr_bc (ϖ.toAinf a))]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨m', hm', h'⟩ := (hE (kappa T (j (E.tr (ϖ.toAinf a) y)))).1 ⟨y, rfl⟩
    exact ⟨_, toW_mem_MA t ϖ P hm', h'.symm⟩
  | zero => exact ⟨0, zero_mem _, by rw [I.j.map_zero, j.map_zero, (kappa T).map_zero]⟩
  | add z z' _ _ h h' =>
    obtain ⟨v, hv, hv'⟩ := h
    obtain ⟨v', hw, hw'⟩ := h'
    exact ⟨v + v', add_mem hv hw, add_step I E j z z' v v' hv' hw'⟩
  | smul c z _ h =>
    obtain ⟨v, hv, hv'⟩ := h
    exact ⟨_, inclO_smul_mem_MA P _ hv, smul_step I E j c z v hv'⟩

theorem core {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (hI : IsBK I)
    (g : ↥(GK (ϖ.field a))) (m : Vec K a ι) (hm : m ∈ P.M) :
    I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) ∈ MA P ∧
      ((g : GQ l) ∈ ϖ.GfieldInf a →
        I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := by
  letI := zlLat T
  obtain ⟨E, j, H, hE⟩ := hI
  obtain ⟨x, hx⟩ := (hE (I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩))).2 ⟨m, hm, rfl⟩
  have hact : I.j (I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) =
      kappa T (j (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))) := by
    rw [Ident.j_act, hx, kappa_act]
    exact congrArg (kappa T) (H.j_act g _).symm
  refine ⟨?_, fun hg => I.j.injective ?_⟩
  · obtain ⟨v, hv, hv'⟩ := span_step I E j hE (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))
    rw [← hact, I.j.injective.eq_iff] at hv'
    exact hv' ▸ hv
  · have h1 : (ainfHom (ϖ.field a) g).comp (ϖ.toAinf a) = ϖ.toAinf a :=
      Hom.ext' (RingHom.ext fun y => PiSys.gal_ev l a ϖ hg y)
    rw [hact, ← E.tr_comp, h1, ← hx]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PhiMod O K l e a ι} {T : Lat a O K ϖ}

theorem act_eb_mem (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (i : ι) :
    I.act (g : GQ l) g (eb i) ∈ MA P := by
  rw [← toW_mb P i]
  exact (core I hI g _ (mb_mem P i)).1

theorem act_MA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ MA P, I.act (g : GQ l) g v ∈ MA P := by
  rintro _ ⟨c, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pi_eq_sum_univ (inclV l O ι c), map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul]
  change galOW O (g : GQ l) (inclO l O (c i)) • _ ∈ _
  rw [galOW_inclO]
  exact inclO_smul_mem_MA P _ (act_eb_mem I hI g i)

theorem act_LA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ LA t ϖ P, I.act (g : GQ l) g v ∈ LA t ϖ P := by
  rintro _ ⟨c, rfl⟩
  have h1 : inclL t ϖ P c = ∑ i, inclO l O (c i) • phiW t ϖ P (eb i) := by
    rw [inclL_apply]
    conv_lhs => rw [pi_eq_sum_univ (fun i => inclO l O (c i)), Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, phiW_eb]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul, galOW_inclO, Ident.act_phiW]
  refine inclO_smul_mem_LA P _ ?_
  obtain ⟨d, hd⟩ := act_eb_mem I hI g i
  rw [← hd, phiW_inclV]
  exact ⟨_, rfl⟩

theorem act_fix (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (hg : (g : GQ l) ∈ ϖ.GfieldInf a)
    (v : ME P) : I.act (g : GQ l) g (toW t ϖ P v) = toW t ϖ P v := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [pi_eq_sum_univ (toW t ϖ P v), map_sum]
  conv_rhs => rw [pi_eq_sum_univ (toW t ϖ P v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ident.act_smul, toW_apply, ϖ.galOW_iW t K hg]
  congr 1
  have h := (core I hI g _ (mb_mem P i)).2 hg
  rw [toW_mb P i] at h
  exact h

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) ∧ ∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK
  refine ⟨fun g => ⟨act_LA _ hBK g, act_MA _ hBK g⟩, fun g hg v => ?_⟩
  exact act_fix (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) hBK
    ⟨sQ l g, PiSys.fixing_fieldInf_le a ϖ hg⟩ hg v

end GlobalTheory.BKGal.StableFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmpSemilinearPair
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal


set_option maxHeartbeats 1600000 in
theorem cmp_semilinear_pair : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (μ : OA l O), IsUnit (toB l O μ) → (∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O μ • v) = TWincl (inclO l O) T z) → ∀ (σA : OA l O →ₐ[O] OA l O) (σW : OW l O →ₐ[O] OW l O) (σB : OB l O →ₐ[O] OB l O) (h : ↥T.L.T →ₗ[O] ↥T.L.T) (F : (ι → OW l O) →ₗ[O] (ι → OW l O)) (lam : OA l O) (Γ : Matrix ι ι (OA l O)), (∀ x, inclO l O (σA x) = σW (inclO l O x)) → (∀ x, toB l O (σA x) = σB (toB l O x)) → (∀ v, I.j (F v) = TensorProduct.map σW.toLinearMap h (I.j v)) → (∀ (r : OW l O) v, F (r • v) = σW r • F v) → (∀ c, inclO l O lam • F (inclL t ϖ P c) = inclL t ϖ P (Γ *ᵥ fun i => σA (c i))) → ∀ v : ι → OB l O, jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB hC μ hμ hL σA σW σB h F lam Γ h1 h2 h3 h4 h5

  have hmapB : ∀ (r : OB l O) (z : TW (OB l O) T),
      TensorProduct.map σB.toLinearMap h (r • z) = σB r • TensorProduct.map σB.toLinearMap h z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
    | tmul b x => simp [TensorProduct.smul_tmul', TensorProduct.map_tmul]
  have hmapW : ∀ z : TW (OA l O) T, TensorProduct.map σW.toLinearMap h (TWincl (inclO l O) T z) =
      TWincl (inclO l O) T (TensorProduct.map σA.toLinearMap h z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b x => simp [TWincl, TensorProduct.map_tmul, h1]
  have hmapBA : ∀ z : TW (OA l O) T, TensorProduct.map σB.toLinearMap h (TWincl (toB l O) T z) =
      TWincl (toB l O) T (TensorProduct.map σA.toLinearMap h z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b x => simp [TWincl, TensorProduct.map_tmul, h2]
  have hsmulL : ∀ (m : OA l O) (c : ι → OA l O), inclO l O m • inclL t ϖ P c = inclL t ϖ P (m • c) := by
    intro m c
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    congr 1
    funext k
    simp [map_mul]
  have htoB : ∀ (m : OA l O) (c : ι → OA l O), (fun k => toB l O ((m • c) k)) = toB l O m • fun k => toB l O (c k) := by
    intro m c; funext k; simp [map_mul]

  have key : ∀ i : ι, jB (fun k => toB l O (Γ k i)) =
      toB l O lam • TensorProduct.map σB.toLinearMap h (jB (Pi.single i 1)) := by
    intro i
    set c : ι → OA l O := Pi.single i 1 with hc
    have hcB : (fun k => toB l O (c k)) = (Pi.single i 1 : ι → OB l O) := by
      funext k; by_cases hk : k = i
      · subst hk; simp [hc]
      · simp [hc, Pi.single_apply, hk]
    obtain ⟨z, hz⟩ := hL (inclL t ϖ P c) ⟨c, rfl⟩
    rw [hsmulL] at hz
    have hz1 : toB l O μ • jB (Pi.single i 1) = TWincl (toB l O) T z := by
      rw [← hC _ _ hz, htoB, hcB, map_smul]
    have hσc : (fun k => σA ((μ • c) k)) = σA μ • c := by
      funext k; by_cases hk : k = i
      · subst hk; simp [hc]
      · simp [hc, Pi.single_apply, hk]
    have hF : I.j (inclL t ϖ P (σA μ • (Γ *ᵥ c))) =
        TWincl (inclO l O) T (lam • TensorProduct.map σA.toLinearMap h z) := by
      rw [← Matrix.mulVec_smul, ← hσc, ← h5, map_smul, h3, hz, hmapW, GlobalTheory.Cyc.Decomp.TWincl_smul]
    have h6 := hC _ _ hF
    rw [htoB, GlobalTheory.Cyc.Decomp.TWincl_smul, ← hmapBA, ← hz1, hmapB, h2, map_smul] at h6
    have hΓ : (fun k => toB l O ((Γ *ᵥ c) k)) = fun k => toB l O (Γ k i) := by
      funext k; simp [hc, Matrix.mulVec_single]
    rw [hΓ, smul_comm (toB l O lam)] at h6
    exact ((hμ.map σB).smul_left_cancel).1 h6
  intro v
  let Pr : (ι → OB l O) → Prop := fun v =>
    jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v)
  have h0 : Pr 0 := by
    have h00 : (fun i => σB ((0 : ι → OB l O) i)) = 0 := by funext i; simp
    simp only [Pr]
    rw [h00, Matrix.mulVec_zero, map_zero, map_zero, smul_zero]
  have hadd : ∀ v w, Pr v → Pr w → Pr (v + w) := by
    intro v w hv hw
    simp only [Pr] at hv hw ⊢
    have : (fun i => σB ((v + w) i)) = (fun i => σB (v i)) + fun i => σB (w i) := by
      funext i; simp
    rw [this, Matrix.mulVec_add, map_add (f := _), hv, hw, map_add (f := _), map_add (f := _), smul_add]
  have hsm : ∀ (r : OB l O) v, Pr v → Pr (r • v) := by
    intro r v hv
    simp only [Pr] at hv ⊢
    have : (fun i => σB ((r • v) i)) = σB r • fun i => σB (v i) := by
      funext i; simp [map_mul]
    rw [this]
    rw [Matrix.mulVec_smul]
    rw [map_smul, hv, map_smul, hmapB]
    rw [smul_smul, smul_smul, mul_comm]
  have hbas : ∀ i, Pr (Pi.single i 1) := by
    intro i
    simp only [Pr]
    have : (fun k => σB ((Pi.single i 1 : ι → OB l O) k)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [this, Matrix.mulVec_single]
    convert key i using 2
    funext k; simp
  have hv : v = ∑ i, v i • (Pi.single i 1 : ι → OB l O) := by
    funext k; simp [Finset.sum_apply, Pi.single_apply]
  have := Finset.sum_induction (s := Finset.univ) (fun i => v i • (Pi.single i 1 : ι → OB l O)) Pr hadd h0
    (fun i _ => hsm _ _ (hbas i))
  rw [← hv] at this
  exact this

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContChiRat
section
noncomputable section

namespace GlobalTheory.HfCharProof

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem act_chiRat (c : ℕ) (g : Br.G D.nbr i w hw) (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x =
      (D.nbr i w hw).toLL (((chiU D.nd i c * (chiU D.nd i 1)⁻¹)
        (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) • x := by
  funext b
  rw [Subsingleton.elim b 0]
  change (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec x 0 = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
  congr 1
  change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) = _
  congr 1
  simp [chiRatO, twistM]

theorem cont_chiRat (c : ℕ) (x : Fin 1 → Br.LL D.nbr i w hw) :
    Continuous fun g => matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x := by
  simp only [act_chiRat]
  have hs : Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  have hL : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => (D.nbr i w hw).toLL
      ((D.nd.chi i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      (D.nbr i w hw).toLL
      ((D.nd.chi i 1 (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) : (D.nd.O i)ˣ) : D.nd.O i) :=
    (hL.comp ((D.nd.chi_cont i c).comp hs)).mul
      (hL.comp ((D.nd.chi_cont i 1).comp (hs.comp continuous_inv)))
  refine Continuous.smul (h1.congr fun g => ?_) continuous_const
  rw [← map_mul, ← Units.val_mul, map_inv, map_inv, map_inv]
  rfl

theorem chiRat_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Formalism.MainNotions.N.GE D.nd) :
    (chiU D.nd i (n + 1) * (chiU D.nd i 1)⁻¹) g = (epsU D.nd i g)⁻¹ ^ n := by
  rcases hn with rfl | hc
  · simp
  · have h := D.nd.chi_def i (n + 1) (by omega) hc
    change D.nd.chi i (n + 1) g * (D.nd.chi i 1)⁻¹ g = _
    rw [mul_comm, h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl

theorem eps_eq (g : Br.G D.nbr i w hw) :
    (D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  rw [Br.PD, (D.loc _).PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
  exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)

theorem act_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Br.G D.nbr i w hw)
    (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i (n + 1))) g x =
      ((algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹) ^ n • x := by
  rw [act_chiRat, chiRat_eq D i n hn, Units.val_pow_eq_pow_val, map_pow, map_units_inv, eps_eq]

def chiLat (c : ℕ) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) where
  V := Fin 1 → Br.LL D.nbr i w hw
  ρ := matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))
  cont := cont_chiRat D i w hw c
  L := Br.locLat D.nbr i w hw (chiRatO D.nd i c)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem hfChar : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LocalSituation.Conclusion4 D HW F → InertEq D →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      D.nd.l i ≠ 2 → (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 → HfChar i w hw := by
  intro D HW F h4 hI i w hw h2 hK
  have hs := (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 hK
  have hT := (h4 (D.nd.l i) _ 1 _ hs).2
  have hr : ∀ c, finrank (Br.LL D.nbr i w hw) (chiLat D i w hw c).V = 1 := fun c =>
    Module.finrank_fin_fun _
  refine ⟨fun c hc => ?_, fun f hf => ?_⟩
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    exact ((hT n (chiLat D i w hw (n + 1)) (hr _) (act_eq D i w hw n (Or.inr hc2))).2.1 (by omega)).le
  · obtain ⟨-, x, hx⟩ :=
      ((hT 0 (chiLat D i w hw 1) (hr _) (act_eq D i w hw 0 (Or.inl rfl))).2.2 rfl f).1 hf
    refine ⟨x, fun g hg => hx g ?_⟩
    rw [hI i w hw] at hg
    exact hg

end GlobalTheory.HfCharProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpsOfExactDegreeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_character_jumps_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = d τ then 1 else 0 := by
  first | exact @GlobalTheory.Per.CharJumps.jumps_of_exact_degree | exact GlobalTheory.Per.CharJumps.jumps_of_exact_degree | (intros; apply GlobalTheory.Per.CharJumps.jumps_of_exact_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscBoundedFunctionIsPowerSeriesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disc_bounded_function_isPowerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  first | exact @GlobalTheory.BSP.disc_bdd_isSeries | exact GlobalTheory.BSP.disc_bdd_isSeries | (intros; apply GlobalTheory.BSP.disc_bdd_isSeries <;> assumption)
end

