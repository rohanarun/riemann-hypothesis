module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniformisationLawsOfBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumSectionsOfFiniteSumsOnThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.SecAdicSum

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

theorem sumI_of_ker {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (A : Matrix (Fin b) (Fin a) R) {E Ix : Type} [AddCommGroup E] [Module R E] (ev : (Fin a → R) →ₗ[R] E)
    (v : Ix → Fin a → R) (v₀ : Fin a → R) (hv : ∀ i, A.mulVec (v i) = 0) (hv₀ : A.mulVec v₀ = 0)
    (h : ∀ e : ℕ, ∃ S : Finset Ix, ∀ T : Finset Ix, S ⊆ T → ∀ k, (v₀ - ∑ i ∈ T, v i) k ∈ I ^ (e + 1)) :
    SumI I (fun i => ev (v i)) (ev v₀) := by
  let N : Submodule R (Fin a → R) := LinearMap.ker A.mulVecLin
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  refine ⟨N.map ev, (IsNoetherian.noetherian N).map ev, ⟨v₀, hv₀, rfl⟩, fun i => ⟨v i, hv i, rfl⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := h (n + c)
  refine ⟨S, fun T hT => ?_⟩
  have m₁ : v₀ - ∑ i ∈ T, v i ∈ N := N.sub_mem hv₀ (N.sum_mem fun i _ => hv i)
  have m₂ : v₀ - ∑ i ∈ T, v i ∈ I ^ (n + c) • (⊤ : Submodule R (Fin a → R)) := by
    rw [pi_eq_sum_univ (v₀ - ∑ i ∈ T, v i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem_smul
      (Ideal.pow_le_pow_right (Nat.le_succ _) (hS T hT k)) Submodule.mem_top
  have m₃ := (hc (n + c) (Nat.le_add_left _ _)).le ⟨m₂, m₁⟩
  rw [Nat.add_sub_cancel] at m₃
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sub, ← Submodule.map_smul'']
  exact ⟨_, Submodule.smul_mono le_rfl inf_le_right m₃, rfl⟩

section
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X}
  (P : Perf f M)

theorem exists_vec (s : LB.Sec M) :
    ∃ v : Fin P.a → R, P.D₀.mulVec v = 0 ∧ ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i := by
  have h : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E, hE⟩ := P.sec R (RingHom.id R) X (𝟙 X) f h
  have le : ∀ j : PUnit → M.ι, (M.pull (𝟙 X)).U j ≤ M.U (j PUnit.unit) := fun j y hy =>
    Set.mem_iInter.1 hy PUnit.unit
  let t : LB.Sec (M.pull (𝟙 X)) := ⟨fun j => AbLaw.rs X (le j) (s.f (j PUnit.unit)), fun j j' => fn_ext fun y hy => by
    have hm : y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) := ⟨le j hy.1, le j' hy.2⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.1 _)).trans (Eq.trans ?_
      ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans
        (congrArg Units.val (gm_linComb M _ _ (𝟙 X) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y _ hy.2 _)))).symm)
    rw [Fintype.prod_unique, zpow_one]
    exact (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (s.compat _ _)).trans
      ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))⟩
  obtain ⟨v, hv⟩ := E.surjective t
  refine ⟨v.1, v.2, fun i => ?_⟩
  have e := hE v i
  rw [hv] at e
  exact (AbLaw.rs_rs _ _ _).symm.trans e

theorem comp_eq_zero {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) (v : Fin P.a → R) (hv : P.D₀.mulVec v = 0)
    (h0 : ∀ i y, π y ∈ P.W i → gs π y _ (loc₀ P v i) = 0) : g ∘ v = 0 := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  have k₁ : (P.D₀.map g).mulVec (g ∘ v) = 0 := funext fun j =>
    (RingHom.map_mulVec g _ _ j).symm.trans ((congrArg g (congrFun hv j)).trans (map_zero g))
  refine congrArg Subtype.val (E.injective (a₁ := ⟨_, k₁⟩) (a₂ := ⟨0, Matrix.mulVec_zero _⟩) ?_)
  refine Seesaw.sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i))
    (fun y => exists_mem P (π y)) fun i => ?_
  refine (hE _ i).trans (Eq.trans ?_ (hE _ i).symm)
  refine (loc_comp P h v i).trans (Eq.trans (fn_ext (b := 0) fun y hy => ?_) (by simp))
  refine (gs_pull (𝟙 X') π y _ hy _).trans ?_
  rw [Category.id_comp, h0 i y hy, gs_eq (𝟙 X') y (π ⁻¹ᵁ P.W i) hy, map_zero, map_zero]

theorem loc₀_sub_sum {Ix : Type} (v₀ : Fin P.a → R) (v : Ix → Fin P.a → R) (T : Finset Ix) (i : P.I) :
    loc₀ P (v₀ - ∑ j ∈ T, v j) i = loc₀ P v₀ i - ∑ j ∈ T, loc₀ P (v j) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [loc₀, Pi.sub_apply, Finset.sum_apply, map_sub, map_sum, sub_mul, Finset.sum_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

end

section
variable {X Y Z : Scheme.{0}} {L : LB Y} {K : Type} [Fintype K] {φ : K → (X ⟶ Y)} {ε : K → ℤ} {R : Type} [CommRing R]
  {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (LB.LinComb L φ ε))

theorem gs_loc₀ {s : LB.Sec (LB.LinComb L φ ε)} {v : Fin P.a → R}
    (h : ∀ i, AbLaw.rs X (P.le i) (s.f (P.ch i)) = loc₀ P v i) (r : Z ⟶ X) (z : Z) {i : P.I} (hi : r z ∈ P.W i)
    {J : (Z ⟶ Y) → L.ι} (hJ : Good L z J) :
    gs r z _ (loc₀ P v i) = (trF φ ε r z (P.ch i) fun k => J (r ≫ φ k)).val * sval s r z J := by
  rw [← h i]
  exact (gs_res r z (P.le i) hi _).trans (sec_trans s r z (P.le i hi) (hJ.mem φ r))

end

theorem gs_cst_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    {B : Over (Spec (CommRingCat.of R))} (b : TF (R := R) F ⟶ B) (z : (TF (R := R) F).left) (W : B.left.Opens)
    (hz : b.left z ∈ W) (c : R) : gs b.left z W (AbLaw.cst B.hom W c) =
      CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) c)) := by
  have w : b.left ≫ B.hom = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
    rw [Over.w b, Category.id_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  rw [gs_eq b.left z W hz, app_cst w W c]
  exact TopCat.Presheaf.germ_res_apply (TF (R := R) F).left.presheaf _ z hz _

theorem sumF_of_sum_on_thickenings : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro _ R _ _ _ I hR D F _ _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  have hL := D.toPre.P.isLB
  obtain ⟨P⟩ := _root_.GlobalTheory.AbLaw.nonempty_perf_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    set_option synthInstance.maxHeartbeats 100000 in
      rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end GlobalTheory.SecAdicSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
namespace GlobalTheory.PrimVan

theorem cechLB_acyclic_of_primitive :
    ∀ (K : Type) [Field K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B],
      IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB →
      (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M →
      ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → B.left.Opens), (∀ i, IsAffineOpen (D i)) →
        ⨆ i, D i = ⊤ → ∀ n, (cechLB B.hom M D).ExactAt n ∧ IsZero ((cechLB B.hom M D).homology n) ∧
          Module.finrank K ((cechLB B.hom M D).homology n) = 0 := by
  intro K _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n
  have := hB.proper
  have h := acyclic_of_kuenneth GlobalTheory.AbLaw.finrank_cechLB_homology_extProd hB hM (lbIso_pull_mul hM hu) (subsingleton_sec hB hM hu hn)
    hD hc (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ M κ D hM inferInstance hP hD hc)
    (GlobalTheory.AbLaw.cechLB_homology_finite_of_affine_cover K _ _ _ κ D (Inh.trivLB_isLB _) inferInstance hP hD hc) n
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h
  have := ModuleCat.isZero_iff_subsingleton.1 hz
  exact ⟨h, hz, Module.finrank_zero_of_subsingleton⟩

theorem acyclic_cechLB_of_primitive :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) :=
  fun K _ _ B _ _ hB hP M hM hu hn κ _ _ D hD hc n =>
    (cechLB_acyclic_of_primitive K B hB hP M hM hu hn κ D hD hc n).1

end GlobalTheory.PrimVan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.TwistKer

theorem cls_twist_pull {S : Scheme.{0}} (B : Over S) [GrpObj B] {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB)
    {T : Over S} (x : T ⟶ B) (h : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB)
    (h' : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB) :
    CechPic.cls _ h = CechPic.pull (x ▷ B).left (CechPic.cls _ h') := by
  have e₁ : (x ▷ B).left ≫ (snd B B).left = (snd T B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have e₂ : (x ▷ B).left ≫ (lift (fst B B ≫ 𝟙 B) (snd B B) ≫ μ[B]).left =
      (lift (fst T B ≫ x) (snd T B) ≫ μ[B]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_lift, Category.comp_id, whiskerRight_snd, whiskerRight_fst]
  have hx : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h1 : (translDiff B L (𝟙 B)).IsLB := LB.isLB_linComb hL _ _
  rw [CechPic.cls_div hx (pull_isLB hO _), CechPic.cls_div h1 (pull_isLB hO _), map_sub,
    CechPic.cls_pull hO, CechPic.cls_pull hO, ← CechPic.pull_comp, e₁]
  congr 1
  refine (CechPic.cls_linComb hL _ _ hx).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull (x ▷ B).left) (CechPic.cls_linComb hL _ _ h1)).symm
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add (f := _), map_zsmul,
    ← CechPic.pull_comp, e₁, e₂]

theorem exists_closed_twist_kernel : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L O : LB B.left, L.IsLB → O.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ B), IsClosedImmersion j.left ∧ (∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) := by
  intro hG R _ B _ hB hP L O hL hO
  have hF : (LB.div (translDiff B L (𝟙 B)) (O.pull (snd B B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  obtain ⟨H, j, hj, h⟩ := GlobalTheory.T.exists_closedSubscheme_locallyTrivial_product_lineBundle hG R B B hB hP _ hF
  refine ⟨H, j, hj, fun T x => Iff.trans ?_ (h T x)⟩
  have hx : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
    LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
  refine forall_congr' fun p => exists_congr fun U => and_congr Iff.rfl ?_
  refine (CechPic.cls_eq_zero_iff (pull_isLB hx _)).symm.trans
    (Iff.trans ?_ (CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hF _) _)))
  rw [CechPic.cls_pull hx, CechPic.cls_pull (pull_isLB hF _), CechPic.cls_pull hF, cls_twist_pull B hL hO x hx hF]

end GlobalTheory.UU.TwistKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsH1VanishesGeneratedPullbackPowTensorDual
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TwistPair
variable {X W W₁ : Scheme.{0}}

theorem firstCohomologyVanishes_of_refines {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (h : FirstCohomologyVanishes N) :
    FirstCohomologyVanishes M := by
  intro I V d hV hc φ hφ
  have e : ∀ (a b : I) {U : X.Opens} (h₁ : U ≤ M.U (d a) ⊓ M.U (d b)),
      rs X h₁ (M.g (d a) (d b)).val =
        rs X (h₁.trans (inf_le_inf (le _) (le _))) (N.g (c (d a)) (c (d b))).val := fun a b U h₁ => by
    rw [hg]
    exact rs_rs _ _ _
  obtain ⟨ψ, hψ⟩ := h I V (fun a => c (d a)) (fun a => (hV a).trans (le _)) hc φ (fun a b b' => by
    have := hφ a b b'
    rw [e] at this
    exact this)
  refine ⟨ψ, fun a b => ?_⟩
  rw [e]
  exact hψ a b

def secRefine {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (s : LB.Sec N) :
    LB.Sec M where
  f := fun k => rs X (le k) (s.f (c k))
  compat := fun k l => by
    have h := congrArg (rs X (inf_le_inf (le k) (le l))) (s.compat (c k) (c l))
    rw [hg]
    rw [map_mul] at h
    refine (rs_rs _ _ _).trans (((rs_rs _ _ _).symm.trans h).trans ?_)
    exact congrArg₂ (· * ·) rfl ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)

theorem nonzeroLocus_le_secRefine {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (hM : M.IsLB)
    (s : LB.Sec N) : nonzeroLocus s ≤ nonzeroLocus (secRefine c le hg s) := by
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := exists_chart hM x
  refine Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : x ∈ X.basicOpen (rs X (inf_le_left : N.U i ⊓ N.U (c k) ≤ N.U i) (s.f i)) := by
    have := Scheme.basicOpen_res X (s.f i) (homOfLE (inf_le_left : N.U i ⊓ N.U (c k) ≤ N.U i)).op
    exact this.ge ⟨⟨X.basicOpen_le _ hi, le k hk⟩, hi⟩
  have h₂ : x ∈ X.basicOpen (rs X (inf_le_right : N.U i ⊓ N.U (c k) ≤ N.U (c k)) (s.f (c k))) := by
    have := (congrArg X.basicOpen (s.compat i (c k))).le h₁
    rw [Scheme.basicOpen_mul] at this
    exact this.2
  have h₃ := (Scheme.basicOpen_res X (s.f (c k))
    (homOfLE (inf_le_right : N.U i ⊓ N.U (c k) ≤ N.U (c k))).op).le h₂
  exact (Scheme.basicOpen_res X (s.f (c k)) (homOfLE (le k)).op).ge ⟨hk, h₃.2⟩

theorem gm_tw (H : LB X) (a b : W ⟶ X) (t : ℤ) (y : W) (i j i' j' : H.ι)
    (hi : a y ∈ H.U i) (hj : b y ∈ H.U j) (hi' : a y ∈ H.U i') (hj' : b y ∈ H.U j') :
    gm (𝟙 W) y _ ((tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).g
      (fun _ => j, fun _ => i) (fun _ => j', fun _ => i')) =
      gm a y _ (H.g i i') ^ t * gm b y _ (H.g j j') ^ (-1 : ℤ) := by
  have m : ∀ (e : W ⟶ X) (k : H.ι), e y ∈ H.U k → (𝟙 W : W ⟶ W) y ∈ LB.wchart H (K := PUnit) (fun _ => e) (fun _ => k) :=
    fun e k h => Set.mem_iInter.2 fun _ => h
  refine (gm_div (pw (H.pull a) (-t)) (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (𝟙 W) y
    (fun _ => j, fun _ => i) (fun _ => j', fun _ => i') ⟨⟨m b j hj, m a i hi⟩, m b j' hj', m a i' hi'⟩).trans ?_
  have e₁ := gm_linComb H (K := PUnit) (fun _ => b) (fun _ => -1) (𝟙 W) y (fun _ => j) (fun _ => j')
    (m b j hj) (m b j' hj')
  have e₂ := gm_pull_g H a (𝟙 W) y (fun _ => i) (fun _ => i') (m a i hi) (m a i' hi')
  rw [Fintype.prod_unique, Category.id_comp] at e₁
  rw [Category.id_comp] at e₂
  refine (congrArg₂ (fun u v => u * v⁻¹) e₁ ((map_zpow _ _ _).trans (congrArg (· ^ (-t)) e₂))).trans ?_
  simp only [zpow_neg, inv_inv]
  exact mul_comm _ _

theorem gm_pair (H : LB X) (a b : W₁ ⟶ X) (t : ℤ) (σ : W ⟶ W₁) (y : W) (j j' : Fin 2 → H.ι)
    (hj : σ y ∈ LB.wchart H ![a, b] j) (hj' : σ y ∈ LB.wchart H ![a, b] j') :
    gm σ y _ ((LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).g j j') =
      gm (σ ≫ a) y _ (H.g (j 0) (j' 0)) ^ t * gm (σ ≫ b) y _ (H.g (j 1) (j' 1)) ^ (-1 : ℤ) :=
  (gm_linComb H ![a, b] ![t, -1] σ y j j' hj hj').trans (Fin.prod_univ_two _)

theorem twist_pair : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (W X : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of S)) (H : LB X) (a b : W ⟶ X) (n : ℕ) (s : Fin (n + 1) → LB.Sec (H.pull a)), H.IsLB → VeryAmpleBy f (H.pull a) s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → (∀ (W₁ : Scheme.{0}) (σ : W ⟶ W₁) (a₁ b₁ : W₁ ⟶ X), σ ≫ a₁ = a → σ ≫ b₁ = b → FirstCohomologyVanishes ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ)) ∧ ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1])), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro S _ _ W X f H a b n s hH hs
  have hM : (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)).IsLB := LB.isLB_linComb hH _ _
  have hA : (H.pull a).IsLB := LB.isLB_pull hH a
  obtain ⟨t₁, h₁⟩ := _root_.GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 S W f _ n s hA hs _ hM
  obtain ⟨t₂, h₂⟩ := GlobalTheory.TwistGen.twist_generated S W f _ n s hA hs _ hM
  refine ⟨max t₁ t₂, fun t ht => ⟨?_, ?_⟩⟩
  · rintro W₁ σ a₁ b₁ rfl rfl
    have le : ∀ J : PUnit → Fin 2 → H.ι, ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ).U J ≤
        (tw (LB.LinComb H (K := PUnit) (fun _ => σ ≫ b₁) (fun _ => -1)) (H.pull (σ ≫ a₁)) t).U
          (fun _ => J PUnit.unit 1, fun _ => J PUnit.unit 0) := fun J y hy =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (mem_pull.1 hy) 1,
        Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (mem_pull.1 hy) 0⟩
    refine firstCohomologyVanishes_of_refines (M := (LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ) _ le
      (fun J J' => unit_ext fun y hy => ?_) (h₁ t (le_of_max_le_left ht))
    have p := mem_pull.1 hy.1
    have p' := mem_pull.1 hy.2
    refine (gm_pull_g _ σ (𝟙 W) y J J' hy.1 hy.2).trans (Eq.trans ?_ (gm_res (𝟙 W) y _ hy _).symm)
    rw [Category.id_comp]
    exact (gm_pair H a₁ b₁ t σ y _ _ p p').trans (gm_tw H (σ ≫ a₁) (σ ≫ b₁) t y _ _ _ _
      (Set.mem_iInter.1 p 0) (Set.mem_iInter.1 p 1) (Set.mem_iInter.1 p' 0) (Set.mem_iInter.1 p' 1)).symm
  · obtain ⟨m, u, hu⟩ := h₂ t (le_of_max_le_right ht)
    have le : ∀ J : Fin 2 → H.ι, (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).U J ≤
        (tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).U
          (fun _ => J 1, fun _ => J 0) := fun J y hy =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1,
        Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0⟩
    have hg : ∀ J J' : Fin 2 → H.ι, (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).g J J' =
        res (inf_le_inf (le J) (le J'))
          ((tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).g
            (fun _ => J 1, fun _ => J 0) (fun _ => J' 1, fun _ => J' 0)) := fun J J' =>
      unit_ext fun y hy => by
        refine (gm_pair H a b t (𝟙 W) y _ _ hy.1 hy.2).trans (Eq.trans ?_ (gm_res (𝟙 W) y _ hy _).symm)
        rw [Category.id_comp, Category.id_comp]
        exact (gm_tw H a b t y _ _ _ _ (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.1 1)
          (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.2 1)).symm
    refine ⟨m, fun i => secRefine (M := LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]) _ le hg (u i),
      top_unique ?_⟩
    rw [← hu]
    exact iSup_mono fun i => nonzeroLocus_le_secRefine _ le hg (LB.isLB_linComb hH _ _) (u i)

end GlobalTheory.TwistPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FurtherLawsOfLaws
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem furtherLaws_of_laws :
    Laws → DVR.TwistBaseChangeStatement → Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  fun h ht =>
    ⟨laws3, uniformisationLaws_of_baseChange_laws h.polBaseChange h.globalFns h.secBaseChange ht,
      laws5 h.globalFns h.secBaseChange,
      lawsSixth_of_unifUniq h.globalFns h.secBaseChange h.ample⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem homExtension_semiAbelian_dvr_unconditional : HomExtSt :=
  GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional)

end GlobalTheory
end

