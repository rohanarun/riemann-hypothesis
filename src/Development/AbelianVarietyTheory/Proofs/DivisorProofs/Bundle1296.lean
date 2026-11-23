module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmple
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_hasNonzeroSec_pow_of_ample_sub_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hX d hdim L B M hL hB hM hcls hineq

  have hgen : ∀ᶠ n : ℕ in atTop, IsGenerated (lbPow B n) := by
    filter_upwards [hB.eventually_isGloballyGenerated_twist (LB.unitMod X)] with n hn
    obtain ⟨ι, hι, φ, hφ⟩ := hn
    exact (isGloballyGenerated_toMod_iff (isLB_lbPow hB.isLB n)).1
      ⟨ι, hι, φ ≫ (unitTwistIso (X := X) (L := lbPow B n)).hom, epi_comp _ _⟩
  obtain ⟨m, hmB, hm1⟩ := (hgen.and (eventually_ge_atTop 1)).exists

  have hLm : IsAmpleLB (lbPow L m) := (isAmpleLB_pow_iff hL.isLB hm1).2 hL
  have hMm : (lbPow M m).IsLB := isLB_lbPow hM m
  have hclsm : cls (lbPow L m) hLm.isLB = cls (lbPow M m) hMm + cls (lbPow B m) hmB.isLB := by
    rw [CechPic.cls_lbPow hL.isLB m, CechPic.cls_lbPow hM m, CechPic.cls_lbPow hB.isLB m, hcls,
      smul_add]

  have hv : DiffVanish (d + 1 + 1) (chiPic k (structureModule X)) := by
    exact diffVanish_chiPic_of_isProjOver (f := strHom k X) (algebraMap_eq_strHom k X)
      (structureModule X) hX
      (by
        unfold QCoh.suppDim
        exact (topologicalKrullDim_subspace_le _ _).trans hdim)
  have hprod : (∏ _i : Fin (d + 1), (m : ℤ)) = (m : ℤ) ^ (d + 1) := by simp
  have hP : ∀ i, ((Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hB.isLB
    · exact hL.isLB
  have hQ : ∀ i, ((Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hmB.isLB
    · exact hLm.isLB
  have hI : interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) =
      (m : ℤ) ^ (d + 1) * interNum k (structureModule X)
        (Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) := by
    rw [← hprod]
    exact hv.interNum_of_cls_eq_zsmul hP hQ (fun _ => (m : ℤ)) (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (CechPic.cls_lbPow hB.isLB m _).trans (natCast_zsmul _ _).symm
      · exact (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm)
  have hT : topSelfIntersection k (lbPow L m) (d + 1) = (m : ℤ) ^ (d + 1) * topSelfIntersection k L (d + 1) := by
    rw [topSelf_def, topSelf_def, ← hprod]
    exact hv.interNum_of_cls_eq_zsmul (fun _ => hL.isLB) (fun _ => hLm.isLB) (fun _ => (m : ℤ))
      (fun _ => (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm)
  have hpos : (0 : ℤ) < (m : ℤ) ^ (d + 1) := pow_pos (by exact_mod_cast hm1) _
  have hineqm : ((d : ℤ) + 1) * interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) <
      topSelfIntersection k (lbPow L m) (d + 1) := by
    rw [hI, hT, mul_left_comm]
    exact mul_lt_mul_of_pos_left hineq hpos

  obtain ⟨r, hr, hs⟩ :=
    T.algebraic_morse_exists_section_ample_sub_generated k X hX d hdim (lbPow L m) (lbPow B m) (lbPow M m) hLm hmB hMm hclsm hineqm
  refine ⟨m * r, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  refine hs.of_cls_eq (isLB_lbPow hM (m * r)) (isLB_lbPow hMm r) ?_
  rw [CechPic.cls_lbPow hM (m * r), CechPic.cls_lbPow hMm r, CechPic.cls_lbPow hM m, smul_smul,
    mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralRelation
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SecIntegral

theorem exists_integral_relation : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∃ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  intro F _ S hS r e u th hcov
  have hI : AlgebraicGeometry.IsIntegral S.Y := hS.isIntegral
  have hη : IsGenericPoint (genericPoint S.Y) Set.univ := by
    simpa using genericPoint_spec S.Y
  obtain ⟨m, b, hb⟩ := _root_.GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring F (S.Y.residueField (genericPoint S.Y)) (S.baseHom (resPt (genericPoint S.Y))) r e
    (fun i => S.val (resPt (genericPoint S.Y)) (S.comb (u i))) (S.powVal (resPt (genericPoint S.Y)) th)
    (_root_.GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring F S hS r e u th hcov _ hη)
  obtain ⟨a, ha, h0⟩ := GlobalTheory.T.homogeneous_components_of_cone_integral_equation _ _ _ r e m _ _ b hb
  exact ⟨m, a, ha, GlobalTheory.T.linearSystem_relation_of_generic_point F S hI r e u th _ hη m a ha h0⟩

end GlobalTheory.SecIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDblOf
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dblEmb {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) : Matrix (Fin n ⊕ Fin n) (Fin n₁ ⊕ Fin n₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Matrix.fromBlocks ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι) 0 0 ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)

def isoD (d : ℕ) {n n₁ : ℕ} (H : Plane E n n₁) : Set (Matrix (Fin d) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  {u | ∃ z₁ z₂ : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), u = Matrix.vecMulVec z₁ (Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
    Matrix.vecMulVec z₂ (Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x))}

def IsDLevi {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} (H : Plane E n n₁)
    (gd₁ : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁))) (md : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J))) : Prop :=
  md.1.1 *ᵥ Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ∧
  md.1.1 *ᵥ Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x) = Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x) ∧
  md.1.1 * dblEmb H.ι = dblEmb H.ι * gd₁.1.1

def IsDblOf (ψ : AddChar (AF F) ℂ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (χW : Chr F E)
    (om : Rep σ X W)
    (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)) : Prop :=
  ∃ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d), (∀ x, d'.e xᵀ = M.co.e x) ∧
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd ∧
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) dd χW (diagCols (Fin n)) omd ∧
    ∀ (g : UA σ X.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))),
      gd.1.1 = Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂

theorem exists_isDblOf {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') :
    ∃ dd omd, IsDblOf B.ψ M χW om dd omd := by
  obtain ⟨-, ⟨d', hd', -, dd, omd, h1, h2, h3⟩, -⟩ := hP.weil
  exact ⟨dd, omd, d', hd', h1, h2, fun g gd hgd φ₁ h₁ φ₂ h₂ => h3 g gd hgd φ₁ h₁ φ₂ h₂⟩

end GlobalTheory.MixXChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGeometricFibre
section
noncomputable section

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem epi_spMap_field {K L : Type} [Field K] [Field L] (σ : K →+* L) : Epi (spMap σ) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem unitOn_pull_spMap {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  exact (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm

theorem eq_iff_of_add {La G : Type} [AddGroup La] [Group G] (P : La → G)
    (hP : ∀ a b, P (a + b) = P a * P b) (a b : La) : P a = P b ↔ P (-a + b) = 1 := by
  have h := hP a (-a + b)
  rw [add_neg_cancel_left] at h
  rw [h]
  constructor
  · intro e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  · intro e
    rw [e, _root_.mul_one]

theorem exists_eq_of_count {La G : Type} [AddCommGroup La] [Module.Finite ℤ La] [Group G] (n : ℕ) (hn : 0 < n)
    (P Q : La → G) (hPa : ∀ a b, P (a + b) = P a * P b) (hQa : ∀ a b, Q (a + b) = Q a * Q b)
    (hP : ∀ a, P a = 1 ↔ ∃ b, a = n • b) (hQ : ∀ a, Q a = 1 ↔ ∃ b, a = n • b)
    (hPQ : ∀ a, ∃ c, P a = Q c) (c : La) : ∃ a, P a = Q c := by
  let m : La →+ La := AddMonoidHom.mk' (fun a : La => n • a) (fun a b => smul_add n a b)
  let K : AddSubgroup La := m.range
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = n • b := fun a => by
    simp only [K, AddMonoidHom.mem_range]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have : AddGroup.FG La := Module.Finite.iff_addGroup_fg.1 inferInstance
  have : Finite (La ⧸ K) := AddCommGroup.finite_of_fg_torsion _ fun q => by
    induction q using QuotientAddGroup.induction_on with
    | H a =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hK]
      exact ⟨a, rfl⟩
  have hmk : ∀ (R : La → G), (∀ a b, R (a + b) = R a * R b) → (∀ a, R a = 1 ↔ ∃ b, a = n • b) →
      ∀ a b, R a = R b ↔ (a : La ⧸ K) = b := fun R hRa hR a b => by
    rw [eq_iff_of_add R hRa, QuotientAddGroup.eq, hK, hR]
  choose f hf using hPQ
  let g : La ⧸ K → La ⧸ K := fun q => (f q.out : La ⧸ K)
  have hg : Function.Injective g := fun q q' e => by
    have e' := (hmk Q hQa hQ _ _).2 e
    rw [← hf, ← hf, hmk P hPa hP] at e'
    simpa using e'
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hg) (c : La ⧸ K)
  refine ⟨q.out, ?_⟩
  rw [hf, hmk Q hQa hQ]
  exact hq

end GlobalTheory.UPel.GeometricLevelExistence

namespace GlobalTheory.UPel.GeometricLevelExistence

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

end GlobalTheory.UPel.GeometricLevelExistence
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviPlane

variable {R : Type} [CommRing R] (c : R →+* R) {n : ℕ}

def fm (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

def lev (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) : Matrix (Fin n) (Fin n) R :=
  1 + (s - 1) • Matrix.vecMulVec X (J *ᵥ fun i => c (Y i)) - (r - 1) • Matrix.vecMulVec Y (J *ᵥ fun i => c (X i))

theorem lev_mulVec (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) (w : Fin n → R) :
    lev c J X Y s r *ᵥ w = w + ((s - 1) * fm c J w Y) • X - ((r - 1) * fm c J w X) • Y := by
  ext i
  simp only [lev, fm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm w]
  ring

theorem fm_skew (hc : ∀ x, c (c x) = x) (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = -J i j)
    (p q : Fin n → R) : fm c J p q = -c (fm c J q p) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fm, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

variable {c}

theorem fm_add_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u + u') v = fm c J u v + fm c J u' v := by
  simp [fm, add_dotProduct]

theorem fm_sub_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u - u') v = fm c J u v - fm c J u' v := by
  simp [fm, sub_dotProduct]

theorem fm_smul_left (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J (a • u) v = a * fm c J u v := by
  simp [fm, smul_dotProduct]

theorem fm_add_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v + v') = fm c J u v + fm c J u v' := by
  have : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_add, dotProduct_add]

theorem fm_sub_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v - v') = fm c J u v - fm c J u v' := by
  have : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_sub, dotProduct_sub]

theorem fm_smul_right (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J u (a • v) = c a * fm c J u v := by
  have : (fun i => c ((a • v) i)) = c a • fun i => c (v i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem entry (J M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Mᵀ * J * M.map c) i j = fm c J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [fm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
variable {R : Type} [CommRing R] {c : R →+* R} {n : ℕ}

section Plane
variable (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
  (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1)
include hc hJ hxx hyy hxy

theorem fm_yx : fm c J Y X = -1 := by rw [fm_skew c hc J hJ, hxy, map_one]

theorem lev_mul (s r s' r' : R) : lev c J X Y s r * lev c J X Y s' r' = lev c J X Y (s * s') (r * r') := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have key : ∀ w, (lev c J X Y s r * lev c J X Y s' r') *ᵥ w = lev c J X Y (s * s') (r * r') *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, lev_mulVec, lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, hxx, hyy, hxy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem lev_one : lev c J X Y 1 1 = 1 := by simp [lev]

theorem lev_unitary (s r : R) (hsr : s * c r = 1) :
    (lev c J X Y s r)ᵀ * J * (lev c J X Y s r).map c = J := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have hrs : r * c s = 1 := by
    have := congrArg c hsr; rw [map_mul, hc, map_one] at this; rw [mul_comm]; exact this
  have key : ∀ u v, fm c J (lev c J X Y s r *ᵥ u) (lev c J X Y s r *ᵥ v) = fm c J u v := by
    intro u v
    rw [lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, fm_add_right, fm_sub_right, fm_smul_right, hxx, hyy, hxy, hyx]
    rw [fm_skew c hc J hJ X v, fm_skew c hc J hJ Y v]
    simp only [map_mul, map_sub, map_one, map_neg]
    linear_combination (-(fm c J u Y * c (fm c J v X))) * hsr + (fm c J u X * c (fm c J v Y)) * hrs
  ext i j
  rw [entry, key]
  have h1 := entry (c := c) J 1 i j
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one,
    Matrix.one_mulVec] at h1
  exact h1.symm

end Plane

theorem lev_X {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} (hxx : fm c J X X = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ X = s • X := by
  rw [lev_mulVec, hxx, hxy]; ext i; simp; ring

theorem lev_Y (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
    (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ Y = r • Y := by
  rw [lev_mulVec, hyy, fm_yx hc hJ hxx hyy hxy]; ext i; simp; ring

theorem lev_mul_ι {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} {k : ℕ} (ι : Matrix (Fin n) (Fin k) R)
    (hι : ∀ j, fm c J (fun i => ι i j) X = 0 ∧ fm c J (fun i => ι i j) Y = 0) (s r : R) :
    lev c J X Y s r * ι = ι := by
  ext i j
  have h := congrFun (lev_mulVec c J X Y s r (fun i => ι i j)) i
  rw [(hι j).1, (hι j).2] at h
  simp only [mul_zero, zero_smul, add_zero, sub_zero] at h
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct] using h

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, Algebra.TensorProduct.map_tmul, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cAr_inclR (σ : E →ₐ[F] E) (e : E) :
    (cA σ).toRingHom (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := cA_inclR σ e

theorem fm_inc (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    fm (cA σ).toRingHom (incM F J) (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fm, form, incV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
    AlgHom.coe_toRingHom, cAr_inclR, cA_inclR]

end GlobalTheory.LeviPlane

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Gen

variable {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def fR (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

variable {c J}
variable {x y : Fin n → R} (hxx : fR c J x x = 0) (hyy : fR c J y y = 0) (hxy : fR c J x y = 1)
  (hyx : fR c J y x = -1)
include hxx hyy hxy hyx

end Gen

end GlobalTheory.AdelicPlaneLevi

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem sigma_invol {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

end Main

end GlobalTheory.AdelicPlaneLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowIdempotentAdelicLatticeModPrimeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_idempotent_adelicLattice_mod_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl (F := F)) (p : ℕ), 0 < p → (p : 𝓞 F) ∈ v.asIdeal →
    ∀ f : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z ∈ GlobalTheory.InertSph.latAt W v, f *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, (f ^ (2 * N)) *ᵥ z - (f ^ N) *ᵥ z = p • y := by
  first | exact @GlobalTheory.LatIdem.exists_pow_idem | exact GlobalTheory.LatIdem.exists_pow_idem | (intros; apply GlobalTheory.LatIdem.exists_pow_idem <;> assumption)
end

