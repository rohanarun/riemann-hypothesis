module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Formalism.JacquetSubsetSums.JacquetSubsetSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.ProdSupport

theorem piTensor_mulSingle {α : Type} [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (a : α) (g : Γ a) (c : ℂ) (h : ∀ v, ρ a g v = c • v) (y : ⨂[ℂ] a, X a) :
    piTensor ρ (Pi.mulSingle a g) y = c • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have h1 : (fun b => ρ b (Pi.mulSingle (M := Γ) a g b) (x b)) = Function.update x a (c • x a) := by
      funext b
      by_cases hb : b = a
      · subst hb
        simp [h]
      · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
    rw [h1, MultilinearMap.map_update_smul, Function.update_eq_self]
    simp

theorem nontrivial_piTensor {α : Type} [Fintype α] (X : α → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (h : ∀ a, Nontrivial (X a)) : Nontrivial (⨂[ℂ] a, X a) := by
  have h1 : ∀ a, ∃ (x : X a) (l : Module.Dual ℂ (X a)), l x = 1 := fun a => by
    obtain ⟨x, hx⟩ := exists_ne (0 : X a)
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
    exact ⟨x, l, hl⟩
  choose x l hl using h1
  refine ⟨PiTensorProduct.tprod ℂ x, 0, fun h0 => ?_⟩
  have := congrArg
    (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
  simp [hl] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_scalar_one {d : ℕ} (hd : d = 1) (z : kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin d) z) = z := by
  ext; simp [GeneralLinearGroup.scalar, hd]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eq_scalar_det {d : ℕ} (hd : d = 1) (g : GL (Fin d) k) :
    g = GeneralLinearGroup.scalar (Fin d) (GeneralLinearGroup.det g) := by
  subst hd
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [GeneralLinearGroup.scalar, GeneralLinearGroup.val_det_apply]

theorem hasCentralChar_multiProd {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (a : α) (ha : ∀ b, b ≠ a → IsEmpty (c b))
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar (σ a) ω) : HasCentralChar (multiProd e σ) ω := by
  intro z f
  have h1 : leviEmb k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) =
      GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    obtain rfl : b = a := by_contra fun h => (ha b h).elim y
    obtain rfl : b' = b := by_contra fun h => (ha b' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp c a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne
      simp
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne'
      simp
  have h3 : deltaHalf k c (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun b _ => ?_
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (Pi.mulSingle a (GeneralLinearGroup.scalar (c a) z))⟩ x
  rw [leviProj_leviEmb, h3, piTensor_mulSingle σ a _ _ (hω z)] at h4
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (ω z : ℂ) • f.1.1 x
  rw [hc, ← h1]
  simpa using h4

theorem exists_inSupport_of_multiProd : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α : Type) [Fintype α] [LinearOrder α]
    (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (χ : kˣ →* ℂˣ),
    (∀ a, IsSmooth (ρ a)) → (∀ a, (ρ a).IsIrreducible) → InSupport (multiProd e ρ) χ →
      ∃ a, InSupport (ρ a) χ := by
  intro hG k _ _ _ _ α _ _ m _ _ n _ _ e X _ _ ρ χ hs hi
  rintro ⟨r, d, e', a, ha, Y, _, _, τ, hτ, hsub, hact⟩
  obtain ⟨b, f, g, s, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e' hs
    (fun i => hasFiniteLength_of_isIrreducible (hi i)) hτ hsub
  have hsum : ∑ i, b.1 i a = 1 := by simpa [ha] using b.2.2 a
  obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => b.1 j a) (Finset.mem_univ i)
  have hi1 : b.1 i a = 1 := by simp only at hsplit; omega
  have hz : ∀ j, j ≠ i → IsEmpty (Fin (b.1 j a)) := fun j hj => by
    have h0 : ∑ j ∈ Finset.univ.erase i, b.1 j a = 0 := by simp only at hsplit; omega
    rw [Finset.sum_eq_zero_iff.1 h0 j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]
    infer_instance
  obtain ⟨ω, -, hω⟩ := LocGL.exists_smooth_hasCentralChar (s i a).smooth (s i a).irr
  have hcen := hasCentralChar_multiProd (g a) (fun j => (s j a).ρ) i hz hω
  obtain rfl : χ = ω := by
    have := Model.nontrivial_of_isIrreducible hτ
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    refine MonoidHom.ext fun z => ?_
    have h1 := Model.scalar_of_isSubquotient hcol
      (piTensor_mulSingle (fun j => multiProd (g j) fun i => (s i j).ρ) a _ _ (hcen z)) y
    rw [hact, det_scalar_one ha] at h1
    exact Units.ext (smul_left_injective ℂ hy h1)
  obtain ⟨Z, _, _, υ, hυ, hυs⟩ := IrrSubquot.exists_irreducible_subquotient _ _
    (piTensor fun j => (s i j).ρ)
    (nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (s i j).irr)
  refine ⟨i, r, b.1 i, f i, a, hi1, Z, _, _, υ, hυ, hυs.trans (hrow i), fun h y => ?_⟩
  refine Model.scalar_of_isSubquotient hυs (piTensor_mulSingle (fun j => (s i j).ρ) a h _ fun v => ?_) y
  conv_lhs => rw [eq_scalar_det hi1 h]
  exact hω _ v

end GlobalTheory.ProdSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BoundaryMaps

section General

variable {G H V W U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


end Local

section Products

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (g : ∀ a, Γ a) (c : α → ℂ) (h : ∀ a x, ρ a (g a) x = c a • x) (y : ⨂[ℂ] a, X a) :
    piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod]
    simp only [h, MultilinearMap.map_smul_univ, RingHom.id_apply]
    rw [smul_comm]

theorem deltaHalf_scalar {α : Type} (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) :
    deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have h1 : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) :=
    fun a => by ext; simp [GeneralLinearGroup.scalar]
  have h2 : ∑ a, modExp m a * (Fintype.card (m a) : ℤ) = 0 := by
    simp only [modExp, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_filter, ite_mul,
      zero_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    simp only [mul_comm]
  apply Units.ext
  rw [val_deltaHalf, modulus]
  have h3 : ∀ a, nabs k (z ^ Fintype.card (m a)) ^ modExp m a =
      nabs k z ^ (modExp m a * (Fintype.card (m a) : ℤ)) := fun a => by
    rw [mul_comm, _root_.zpow_mul, zpow_natCast]
    simp [nabs]
  simp only [h1, h3, ← Real.rpow_intCast]
  rw [← Real.rpow_sum_of_pos (_root_.GlobalTheory.SmGL.nabs_pos' k z), ← Int.cast_sum, h2]
  simp

theorem multiProd_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))
    (ω : α → kˣ →* ℂˣ) (h : ∀ a, HasCentralChar (ρ a) (ω a)) (z : kˣ) (f) :
    multiProd e ρ (GeneralLinearGroup.scalar n z) f = (∏ a, (ω a z : ℂ)) • f := by
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp [leviEmb, blockDiagonal'_apply_eq, GeneralLinearGroup.scalar, diagonal_apply]
    · simp [leviEmb, blockDiagonal'_apply_ne _ _ _ hab, GeneralLinearGroup.scalar,
        diagonal_apply, hab]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have hm : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) ∈ parab k e := by
    apply mem_parab_iff.2
    intro a b i j hab
    rw [h1]
    simp [GeneralLinearGroup.scalar, diagonal_apply, hab.ne']
  have hp : leviProj k e ⟨_, hm⟩ = (fun a => GeneralLinearGroup.scalar (m a) z) := by
    funext a
    ext i j
    simp [leviProj, diagBlock, leviEmb, GeneralLinearGroup.scalar, diagonal_apply]
  have h2 := parInd_law e _ f ⟨_, hm⟩ x
  rw [hp, deltaHalf_scalar, piTensor_scalar ρ _ _ fun a => h a z] at h2
  have h3 : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (_ : ℂ) • f.1.1 x
  rw [h3, ← h1]
  simpa using h2

end Products

end GlobalTheory.BoundaryMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieAlgebraExpEqOfCommuteCartanInvolution
section
open Matrix

namespace GlobalTheory.ExpCartan

open scoped Matrix.Norms.L2Operator ComplexOrder


open scoped MatrixOrder in
theorem exists_posDef_mul_self {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, S.PosDef ∧ S * S = P := by
  refine ⟨CFC.sqrt P, ?_, CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg⟩
  have hP' := hP
  rw [← isStrictlyPositive_iff_posDef] at hP' ⊢
  exact IsStrictlyPositive.sqrt _ hP'

theorem im_star_dotProduct_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M)
    (x : Fin n → ℂ) : (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM]
  exact Complex.conj_eq_iff_im.1 h

theorem exists_exp_eq_of_commute_cartan : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C →
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  intro n G C g hG hC hg hgC
  obtain ⟨hCC, hCG, hpos⟩ := hC
  have hCG' : Cᴴ * G * C = G := by
    have h := congrArg Matrix.transpose hCG
    simpa [Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc] using h
  have hCG2 : Cᴴ * G = G * C := by
    calc Cᴴ * G = Cᴴ * G * (C * C) := by rw [hCC, Matrix.mul_one]
      _ = G * C := by rw [← Matrix.mul_assoc, hCG']
  set P := G * C with hPdef
  have hPh : Pᴴ = P := by rw [hPdef, Matrix.conjTranspose_mul, hG, hCG2]
  have hPpd : P.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hPh, fun x hx => ?_⟩
    have h1 := hpos x hx
    have he : (C *ᵥ x) ⬝ᵥ Gᵀ *ᵥ star x = star x ⬝ᵥ P *ᵥ x := by
      rw [dotProduct_comm, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
        hPdef, ← Matrix.mulVec_mulVec]
    rw [he] at h1
    exact Complex.lt_def.2 ⟨by simpa using h1, by simpa using (im_star_dotProduct_mulVec hPh x).symm⟩
  obtain ⟨S, hSpd, hSS⟩ := exists_posDef_mul_self hPpd
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  set Si := S⁻¹ with hSidef
  have h1 : S * Si = 1 := Matrix.mul_nonsing_inv _ hSu
  have h2 : Si * S = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSih : Siᴴ = Si := by rw [hSidef, Matrix.conjTranspose_nonsing_inv, hSh]
  have hgP : gᴴ * P * g = P := by
    calc gᴴ * P * g = gᴴ * G * (C * g) := by rw [hPdef]; simp only [Matrix.mul_assoc]
      _ = gᴴ * G * g * C := by rw [← hgC.eq]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hg]
  set u := S * g * Si with hudef
  have hsu : star u = Si * gᴴ * S := by
    rw [hudef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih,
      Matrix.mul_assoc]
  have huu : star u * u = 1 := by
    rw [hsu, hudef]
    calc Si * gᴴ * S * (S * g * Si) = Si * (gᴴ * (S * S) * g) * Si := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSS, hgP, ← hSS, ← Matrix.mul_assoc, h2, Matrix.one_mul, h1]
  have hu : u ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨huu, mul_eq_one_comm.1 huu⟩
  set C' := S * C * Si with hC'def
  have hSC : S * C = C' * S := by rw [hC'def, Matrix.mul_assoc _ Si, h2, Matrix.mul_one]
  have hSiC' : Si * C' = C * Si := by
    rw [hC'def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have huC : Commute u C' := by
    show u * C' = C' * u
    rw [hudef, hC'def]
    calc S * g * Si * (S * C * Si) = S * g * (Si * S) * C * Si := by simp only [Matrix.mul_assoc]
      _ = S * (C * g) * Si := by rw [h2, Matrix.mul_one, Matrix.mul_assoc S g C, hgC.eq]
      _ = S * C * (Si * S) * g * Si := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S * C * Si * (S * g * Si) := by simp only [Matrix.mul_assoc]
  have huC' : Commute (star u) C' := by
    have hus : u * star u = 1 := mul_eq_one_comm.1 huu
    show star u * C' = C' * star u
    calc star u * C' = star u * (C' * (u * star u)) := by rw [hus, Matrix.mul_one]
      _ = star u * (u * C' * star u) := by rw [huC.eq]; simp only [Matrix.mul_assoc]
      _ = (star u * u) * C' * star u := by simp only [Matrix.mul_assoc]
      _ = C' * star u := by rw [huu, Matrix.one_mul]
  have hN : IsStarNormal u := ⟨by
    show star u * u = u * star u
    rw [huu, mul_eq_one_comm.1 huu]⟩
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  set Y := cfc Complex.log u with hYdef
  have hlog : ContinuousOn Complex.log (spectrum ℂ u) := hfin.continuousOn _
  have hexp : NormedSpace.exp Y = u := by
    rw [hYdef, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp Complex.exp Complex.log u (hf := hlog) (ha := hN)]
    conv_rhs => rw [← cfc_id' ℂ u hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by intro h; have := hsph z hz; rw [h] at this; simp at this
    simp [Complex.exp_log hz0]
  have hstar : star Y = -Y := by
    rw [hYdef, ← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    apply Complex.ext
    · simp [Complex.log_re, hsph z hz]
    · simp
  have hYC : Commute Y C' := huC.cfc huC' Complex.log
  have hYh : Yᴴ = -Y := by rw [← Matrix.star_eq_conjTranspose, hstar]
  refine ⟨Si * Y * S, ?_, ?_, ?_⟩
  · have hGP : G = S * S * C := by
      rw [hSS, hPdef, Matrix.mul_assoc, hCC, Matrix.mul_one]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih, hYh, hGP]
    calc S * (-Y * Si) * (S * S * C) + S * S * C * (Si * Y * S)
        = -(S * Y * (Si * S) * (S * C)) + S * ((S * C) * Si) * Y * S := by
          simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = -(S * (Y * C') * S) + S * (C' * Y) * S := by
          rw [h2, Matrix.mul_one, hSC, Matrix.mul_assoc C' S Si, h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYC.eq, neg_add_cancel]
  · show Si * Y * S * C = C * (Si * Y * S)
    calc Si * Y * S * C = Si * (Y * C') * S := by rw [Matrix.mul_assoc _ S C, hSC]; simp only [Matrix.mul_assoc]
      _ = (Si * C') * Y * S := by rw [hYC.eq]; simp only [Matrix.mul_assoc]
      _ = C * (Si * Y * S) := by rw [hSiC']; simp only [Matrix.mul_assoc]
  · have hSun : IsUnit S := hSpd.isUnit
    rw [hSidef, Matrix.exp_conj' S Y hSun, hexp, hudef, ← hSidef]
    calc Si * (S * g * Si) * S = (Si * S) * g * (Si * S) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ExpCartan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarilyHilbertMultiplicityModel
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem finiteGroup_acts_unitarily_hilbertMultiplicityModel : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) J χ, ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → Function.Injective e → (∀ x, e x ∈ Mult θ M J χ) → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (g0 : G0 L.Pg L.r) (u : H ≃ₗ[ℂ] H), (∀ x v, e (u x) v = actG0 V β L g0 (e x v)) → ∀ x, ‖u x‖ = ‖x‖ := by
  intro D V S θ M β L J χ H _ _ e d μ 𝓕 hin hinj hmem hμ h𝓕 g0 u hact x
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hμ

  have hchoose : ∀ (P Q : ℂ → Prop) (hP : ∃ c, P c) (hQ : ∃ c, Q c), P = Q → hP.choose = hQ.choose := by
    rintro P Q hP hQ rfl; rfl
  have hip : ipM M μ 𝓕 (e (u x)) (e (u x)) = ipM M μ 𝓕 (e x) (e x) := by
    by_cases hk : ∃ κ, IsLevelLift V β L g0 κ
    · obtain ⟨hcpt, hlift⟩ := _root_.GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
      have hκ : hk.choose ∈ levG V β (flagL L) := hlift g0 _ hk.choose_spec
      have hκi : hk.choose⁻¹ ∈ levG V β (flagL L) := inv_mem hκ
      set a : ℂ := (levChi V β (flagL L) hk.choose)⁻¹ with ha_def
      have ha : ‖a‖ = 1 := by rw [ha_def, norm_inv, GlobalTheory.norm_levChi_flagL_eq_one V β L _ hκ, inv_one]
      have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
      have hai : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
      have hU : ∀ v g, e (u x) v g = a * e x v (g * hk.choose) := by
        intro v g
        rw [hact x v]
        simp only [actG0, dif_pos hk, ha_def]
      have hV : ∀ v g, e x v g = a⁻¹ * e (u x) v (g * hk.choose⁻¹) := by
        intro v g
        rw [hU, mul_assoc g, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
      have hm1 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκ
      have hm2 := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup μ _ hcpt _ hκi
      have hiff : ∀ c, IsMultIP M μ 𝓕 (e (u x)) (e (u x)) c ↔ IsMultIP M μ 𝓕 (e x) (e x) c := by
        intro c
        constructor
        · intro hc
          exact _root_.GlobalTheory.isMultiplicityInner_of_unit_twist_shift θ M J χ μ 𝓕 hμ h𝓕 _ _ hai hm2 _ (hmem (u x)) _ (hmem (u x)) _ _ hV hV c hc
        · intro hc
          exact _root_.GlobalTheory.isMultiplicityInner_of_unit_twist_shift θ M J χ μ 𝓕 hμ h𝓕 _ _ ha hm1 _ (hmem x) _ (hmem x) _ _ hU hU c hc
      unfold ipM
      split_ifs with h1 h2 h2
      · exact hchoose _ _ h1 h2 (funext fun c => propext (hiff c))
      · exact absurd (let ⟨c, hc⟩ := h1; ⟨c, (hiff c).1 hc⟩) h2
      · exact absurd (let ⟨c, hc⟩ := h2; ⟨c, (hiff c).2 hc⟩) h1
      · rfl
    ·
      have h0 : e (u x) = 0 := by
        ext v g
        rw [hact x v]
        simp only [actG0, dif_neg hk]
        rfl
      have hux : u x = 0 := hinj (by rw [h0, map_zero])
      have hx : x = 0 := by
        have := congrArg u.symm hux
        simpa using this
      rw [hux, hx]
  have hsq' : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hin, hin, hip]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaStdMaxParab
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.MaxParabIwasawa

theorem iwasawa_stdMaxParab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r a b : ℕ) (h : a + b = r) (g : GL (Fin r) k),
    (∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, g = κ * p) ∧
      ∃ p ∈ stdMaxParab k h, ∃ κ ∈ KO k (Fin r), g = p * κ := by
  intro k _ _ _ _ r a b h g
  have key : ∀ x : GL (Fin r) k, ∃ κ ∈ KO k (Fin r), ∃ p ∈ stdMaxParab k h, x = κ * p := by
    intro x
    obtain ⟨k₀, p, hp, hx⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r x
    have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi =>
      hp (show j < i from by rw [Fin.lt_def]; omega)
    exact ⟨_, ⟨k₀, rfl⟩, p, hpP, hx⟩
  refine ⟨key g, ?_⟩
  obtain ⟨κ, hκ, p, hp, e⟩ := key g⁻¹
  refine ⟨p⁻¹, inv_mem hp, κ⁻¹, inv_mem hκ, ?_⟩
  rw [← mul_inv_rev, ← e, inv_inv]

end GlobalTheory.MaxParabIwasawa
end
end

