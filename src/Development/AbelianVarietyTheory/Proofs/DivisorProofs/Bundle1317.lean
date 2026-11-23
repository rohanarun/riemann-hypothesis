module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.FODef

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]

theorem sqZero : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0 := by
  rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  change TrivSqZeroExt.fst r = 0 at hr
  change TrivSqZeroExt.fst s = 0 at hs
  rw [Submodule.mem_bot]
  ext
  · simp [hr, hs]
  · simp [hr, hs]

theorem constMorV (A₀ : Over (Sp k)) [GrpObj A₀] :
    GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ (sqZero k V)) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
      (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_id]
      congr 1) (𝟙 A₀)

variable {k V}

def IsFilLiftV {A₀ : Over (Sp k)} [GrpObj A₀] {A : Over (Sp (TrivSqZeroExt k V))} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) i)
    (x : HdR A₀) (y : primDR A₀ →ₗ[k] V) : Prop :=
  ∃ d ∈ liftFil (divided₂ (sqZero k V)) h, ∀ c : primDR A₀,
    d ((constMorV k V A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c)

end GlobalTheory.FODef

namespace GlobalTheory.HTUniv

theorem coord {k : Type} [Field k] {d : ℕ} (c : (Fin d → k) →ₗ[k] k) (v : Fin d → k) :
    c v = ∑ j, v j * c (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : Pi.single j (v j) = v j • (Pi.single j (1 : k) : Fin d → k) := by
    ext i; simp [Pi.single_apply]
  rw [e, map_smul, smul_eq_mul]

theorem comp_pi {k : Type} [Field k] {d : ℕ} {P : Type*} [AddCommGroup P] [Module k P]
    (c : (Fin d → k) →ₗ[k] k) (y : Fin d → (P →ₗ[k] k)) :
    c ∘ₗ LinearMap.pi y = ∑ j, c (Pi.single j 1) • y j := by
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.comp_apply, coord c, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pi_apply, smul_eq_mul, mul_comm]

theorem sum_proj_single {k : Type} [Field k] {d : ℕ} (c₀ : Fin d → k) (j : Fin d) :
    (∑ i, c₀ i • LinearMap.proj (R := k) (φ := fun _ : Fin d => k) i) (Pi.single j 1) = c₀ j := by
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  try exact mul_one _

end GlobalTheory.HTUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponent
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.AdeleInfInj

theorem eq_zero_of_piInf_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) z →
    (∀ w, piInf (emb w) z = 0) → z = 0 := by
  intro F E _ _ _ _ _ σ cm emb z hz hinf
  have hx : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra hc
    push_neg at hc
    have h0 : (⊥ : Subalgebra F E) = ⊤ := eq_top_iff.2 fun y _ => Algebra.mem_bot.2 (hc y)
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h0
    rw [cm.2.2.1] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨x, hx0⟩ := hx
  have li : LinearIndependent F ![(1 : E), x] := LinearIndependent.pair_iff.2 fun s t hst => by
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hx0
      refine ⟨-(s / t), ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      rw [map_neg, map_div₀, neg_div', div_eq_iff htE]
      linear_combination -hst
  let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank li (by simp [cm.2.2.1])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have him : ∀ τ : E →+* ℂ, (τ x).im ≠ 0 := fun τ h0 => by
    have hσx : σ x = x := τ.injective (by
      rw [cm.2.2.2]
      exact Complex.conj_eq_iff_im.2 h0)
    have hσ : ∀ y, σ y = y := by
      intro y
      have e := b.ext (f₁ := σ.toLinearMap) (f₂ := LinearMap.id) fun i => by
        fin_cases i
        · simp [hb0]
        · simp [hb1, hσx]
      exact LinearMap.congr_fun e y
    have := cm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y => ?_)))
    exact (cm.2.2.2 τ y).symm.trans (by rw [hσ y])
  let bA := Algebra.TensorProduct.basis (AF F) b
  have hz_eq : z = ∑ i, bA.repr z i ⊗ₜ[F] b i := by
    conv_lhs => rw [← bA.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let u : AF F := ((0 : Ainf F), (1 : Af F))
  have hfin : ∀ i, (bA.repr z i).2 = 0 := fun i => by
    have h1 : bA.repr (u • z) i = u * bA.repr z i := by rw [map_smul]; rfl
    rw [hz u (map_zero _), map_zero, Finsupp.zero_apply] at h1
    have h3 : (0 : Af F) = 1 * (bA.repr z i).2 := congrArg Prod.snd h1
    simpa using h3.symm
  have := cm.1
  have hinf' : ∀ w i, evInf F w (bA.repr z i) = 0 := fun w => by
    have hw := IsTotallyReal.isReal w
    have h := hinf w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz_eq, map_sum, Fin.sum_univ_two] at h
    change InfinitePlace.Completion.extensionEmbedding w (evInf F w (bA.repr z 0)) * (emb w).1 (b 0) +
      InfinitePlace.Completion.extensionEmbedding w (evInf F w (bA.repr z 1)) * (emb w).1 (b 1) = 0 at h
    rw [hb0, hb1, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw] at h
    set r0 := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (evInf F w (bA.repr z 0)) with hr0
    set r1 := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (evInf F w (bA.repr z 1)) with hr1
    have h1 : r1 = 0 := by
      have := congrArg Complex.im h
      simp at this
      exact this.resolve_right (him _)
    have h0 : r0 = 0 := by
      have := congrArg Complex.re h
      simpa [h1] using this
    intro i
    fin_cases i
    · exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).injective (h0.trans (map_zero _).symm)
    · exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).injective (h1.trans (map_zero _).symm)
  have hc : ∀ i, bA.repr z i = 0 := fun i => Prod.ext (funext fun w => hinf' w i) (hfin i)
  rw [hz_eq]
  simp [hc]

end GlobalTheory.AdeleInfInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefect
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.SymTranslate

theorem sym_rigTransl_of_sq : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ _ L hL _ a h
  have hc : ∀ x : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := fun x => by
    rw [Over.comp_left, CechPic.pull_comp,
      GlobalTheory.PrimitiveOverField.pic_field (CechPic.pull x.left (cls L hL))]
    exact map_zero _
  have h1 : CechPic.pull (1 : B ⟶ B).left (cls L hL) = 0 := hc _
  have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) =
      CechPic.pull ((toUnit B ≫ a ^ 2) * 𝟙 B).left (cls L hL) := by
    rw [lam, hc, h1, Over.id_left, CechPic.pull_id, sub_zero, add_zero] at h
    exact sub_left_injective h
  have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ a)⁻¹).left) h2
  rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
  have e1 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
      (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ a)) := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
      Hom.inv_def, Category.id_comp]
  have e2 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ ((toUnit B ≫ a ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ a) := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
      _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
  rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
  have hL' : (GlobalTheory.RigidTranslate.rigTransl L a).IsLB := LB.isLB_linComb hL _ _
  have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ a)).left (cls L hL) := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc, smul_zero, add_zero, one_smul]
    rfl
  exact GlobalTheory.RigSymSubring.sym_of_cls hL' (by rw [h4]; exact h3)

end GlobalTheory.SymTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqOfReal
section
open NumberField Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_eq_of_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), IsStdChar D ψ (-1) →
    ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      (∀ w : WO V W, w.map (finPart D) = 0 → f w = f' w) → f = f' := by
  intro D ψ V W _ f f' hf hf' h
  have h0 : f + (-1 : ℂ) • f' = 0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real
    (GlobalTheory.WeilVacMove.isTheta_add hf (GlobalTheory.WeilVacMove.isTheta_smul (-1) hf')) fun w hw => by
      rw [Pi.add_apply, Pi.smul_apply, h w hw, neg_one_smul, add_neg_cancel]
  rwa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleComapStableSecondMember
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem sumPl_single_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ w, Module.End ℂ (V w)) (a : ι → ℂ) (w : ι) (hL : ∀ v, v ≠ w → L v = 0) :
    sumPl (fun v => L v + a v • (1 : Module.End ℂ (V v))) =
      atPl w (L w) + (∑ v, a v) • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
  have h : ∀ w, atPl w (L w + a w • (1 : Module.End ℂ (V w))) = atPl w (L w) + a w • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro w
    have e := (PiTensorProduct.mapMultilinear ℂ V V).map_update_add (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w)
      (a w • LinearMap.id)
    have e2 := (PiTensorProduct.mapMultilinear ℂ V V).map_update_smul (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (a w)
      LinearMap.id
    simp only [PiTensorProduct.mapMultilinear_apply, Function.update_eq_self, PiTensorProduct.map_id] at e e2
    simp only [atPl]
    rw [Module.End.one_eq_id, Module.End.one_eq_id, e, e2]
    rfl
  have h0 : ∀ v, v ≠ w → atPl v (L v) = (0 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro v hv
    rw [hL v hv]
    exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) v
  simp only [sumPl, h, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_eq_single w (fun v _ hv => h0 v hv) (fun hw => absurd (Finset.mem_univ w) hw)]

theorem stab_comap_of_thetaSubInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ, (∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (τ w))) (C w)) → ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c → ∀ w, GlobalTheory.HoweR.Stab (GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN C hC hact w
  have key : ∀ Z ∈ upq (R w) (S w), ∀ y ∈ N.comap Φ,
      GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w)) Z y
        ∈ N.comap Φ := by
    intro Z hZ y hy
    set Y : ∀ v : InfinitePlace F, Mat (R v) (S v) := Pi.single w Z with hYdef
    have hYw : Y w = Z := by simp [hYdef]
    have hYv : ∀ v, v ≠ w → Y v = 0 := fun v hv => by simp [hYdef, Pi.single_eq_of_ne hv]
    have hY : ∀ v, Y v ∈ upq (R v) (S v) := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [hYw]; exact hZ
      · rw [hYv v hv]; simp [upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin d) R S τ (incM F W.J) Complex.I C hCM hC Y hY
    have hSD := hact γ hγ Y hgen y
    have hD := (actsLaws F (Fin n × Fin d) _ _ (Φ y)).1 _ (fun t => map_zero _) hSD
    have hmem := hN.2.2.2.1 γ hγ (Φ y) hy _ hD
    rw [sumPl_single_add_smul (fun v => fockAct2 (P v) (Q v) (R v) (S v) (Y v)) (fun v => c v * (Y v).trace) w
      (fun v hv => by simp only [hYv v hv, map_zero]), hYw, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul] at hmem
    exact (N.add_mem_iff_left (N.smul_mem _ hy)).1 hmem
  intro Z y hy
  obtain ⟨A, hA, B, hB, rfl⟩ := _root_.GlobalTheory.HoweD.upq_span _ _ Z
  rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact add_mem (key A hA y hy) (Submodule.smul_mem _ _ (key B hB y hy))

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleContainsFirstMemberCoinvariant
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem coinv_atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem coinv_sumPl_tprod (w : ι) (L : ∀ i, Module.End ℂ (V i)) (hL : ∀ i, i ≠ w → L i = 0) (f : ∀ i, V i) :
    sumPl L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L w (f w))) := by
  unfold sumPl
  rw [LinearMap.sum_apply, Finset.sum_eq_single w, coinv_atPl_tprod]
  · intro i _ hi
    rw [coinv_atPl_tprod, hL i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

end Tensor

theorem tensAny_coinv_le_comap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → LinearMap.range Φ = M.Pol ψ τ → ∀ A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ, (∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (τ w))) (A w)) → ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c → GlobalTheory.HoweR.tensAny (fun w => GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN hr A hA hact
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨w, hw⟩, rfl⟩
  let e : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) →ₗ[ℂ] TensD F P Q R S := (PiTensorProduct.tprod ℂ).toLinearMap f w
  have he : ∀ g, e g = PiTensorProduct.tprod ℂ (Function.update f w g) := fun g => rfl
  have key : ∀ Z ∈ upq (P w) (Q w), ∀ g,
      fockAct1 (P w) (Q w) (R w) (S w) Z g - (-c w * Z.trace) • g ∈ (N.comap Φ).comap e := by
    intro Z hZ g
    let Y : ∀ i : InfinitePlace F, Mat (P i) (Q i) := Pi.single w Z
    have hY : ∀ i, Y i ∈ upq (P i) (Q i) := by
      intro i
      by_cases h : i = w
      · subst h
        simpa [Y] using hZ
      · simp [Y, Pi.single_eq_of_ne h, upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin n) P Q τ (incM F X.J) 1 A hCM hA Y hY
    have h1 := hact γ hγ Y hgen (e g)
    have h2 := (actsLaws F (Fin n × Fin d) _ _ 0).1 _ (fun t => map_zero _) h1
    have h3 := hN.2.1 γ hγ _ (hr ▸ LinearMap.mem_range_self Φ (e g)) _ h2
    rw [he, coinv_sumPl_tprod w _ (fun i hi => by simp [Y, Pi.single_eq_of_ne hi])] at h3
    rw [Submodule.mem_comap, Submodule.mem_comap, he]
    simpa [Y, sub_eq_add_neg] using h3
  have hle : GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w) ≤ (N.comap Φ).comap e := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, g, rfl⟩
    obtain ⟨Z₁, h₁, Z₂, h₂, rfl⟩ := _root_.GlobalTheory.HoweD.upq_span _ _ Z
    have h := Submodule.add_mem _ (key Z₁ h₁ g) (Submodule.smul_mem _ Complex.I (key Z₂ h₂ g))
    rw [SetLike.mem_coe]
    convert h using 1
    simp only [map_add (f := _), map_smul, Matrix.trace_add, Matrix.trace_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  have h := hle hw
  rw [Submodule.mem_comap, he, Function.update_eq_self] at h
  exact h

end GlobalTheory.HoweD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
section
noncomputable section

namespace GlobalTheory.ThK.SquareIntegrability

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toGAd {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {c : E} (hc : c ≠ 0) :
    UA σ J ≃* GlobalTheory.AdelicU.GAd σ (c • J.map σ) :=
  MulEquiv.subgroupCongr (GlobalTheory.SiegelSet.ug_eq_hr (J := J) hσ hc)

end GlobalTheory.ThK.SquareIntegrability
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInverseLatticeCountStackedEigenprojections
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusStack

theorem lattice_count_stack : ∀ (D : D7) (m n r : ℕ) (X Y : Matrix (Fin m) (Fin r) D.host.E) (X' Y' : Matrix (Fin r) (Fin m) D.host.E) (c : ℝ), 0 < c → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, Y'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹) * Y'.map (tauE D τ) ∧ X'.map (tauE D τ) * B τ = Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)) * X'.map (tauE D τ) ∧ (1 - X * Y' - Y * X').map (tauE D τ) * B τ = (1 - X * Y' - Y * X').map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  intro D m n r X Y X' Y' c hc L hL
  have hST : Matrix.fromCols X (Matrix.fromCols Y (1 : Matrix (Fin m) (Fin m) D.host.E)) *
      Matrix.fromRows Y' (Matrix.fromRows X' (1 - X * Y' - Y * X')) = 1 := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.one_mul]
    abel
  obtain ⟨N, C, hC, h⟩ := _root_.GlobalTheory.lattice_count_diag_mul D (Fin r ⊕ Fin r ⊕ Fin m) m n _ _ hST L hL
  obtain ⟨C', hC', h'⟩ := GlobalTheory.T.prod_max_one_pow_le_on_siegelTorusCone r m (Module.finrank ℚ D.host.F * (2 * n)) c hc
  refine ⟨N, C * C', mul_nonneg hC hC', fun t ht B hB => ?_⟩
  have htpos : ∀ i, 0 < t i := ht.1
  refine (h (Sum.elim t (Sum.elim (fun i => (t i)⁻¹) (fun _ => (1 : ℝ)))) ?_ B ?_).trans ?_
  · rintro (k | k | k)
    · exact htpos k
    · exact inv_pos.2 (htpos k)
    · exact one_pos
  · intro τ
    obtain ⟨h1, h2, h3⟩ := hB τ
    ext k j
    rcases k with k | k | k
    · have := congrFun (congrFun h1 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h2 k) j
      rw [Matrix.diagonal_mul] at this ⊢
      simpa [Matrix.mul_apply] using this
    · have := congrFun (congrFun h3 k) j
      rw [Matrix.diagonal_mul]
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.fromRows_apply_inr, Sum.elim_inr,
        Complex.ofReal_one, inv_one, one_mul] at this ⊢
      exact this
  · apply ENNReal.ofReal_le_ofReal
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h' t ht) hC

end GlobalTheory.TorusStack
end

