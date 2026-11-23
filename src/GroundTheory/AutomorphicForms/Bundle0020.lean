module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0019
public import GroundTheory.AutomorphicForms.Cartan
public import GroundTheory.AutomorphicForms.SphericalPrincipal
public import GroundTheory.AutomorphicForms.SphericalLaurent

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.LeviCartan
section
noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel

section Smith

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_eq_mul_diagonal_pow_mul_fintype {ϖ : R} (hϖ : Irreducible ϖ)
    (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    ∃ (P Q : GL ι R) (e : ι → ℕ),
      A = (P : Matrix ι ι R) * diagonal (fun i => ϖ ^ e i) * (Q : Matrix ι ι R) := by
  let eq := Fintype.equivFin ι
  obtain ⟨P, Q, e, -, h⟩ := Cartan.exists_eq_mul_diagonal_pow_mul hϖ (reindex eq eq A)
    (by rwa [det_reindex_self])
  let φ := reindexAlgEquiv R R eq.symm
  refine ⟨Units.map φ.toMonoidHom P, Units.map φ.toMonoidHom Q, e ∘ eq, ?_⟩
  have h1 : φ (reindex eq eq A) = A := by
    ext i j
    simp [φ, reindexAlgEquiv_apply]
  have h2 : φ (diagonal fun i => ϖ ^ e i) = diagonal fun i => ϖ ^ (e ∘ eq) i := by
    rw [reindexAlgEquiv_apply, reindex_apply, Equiv.symm_symm, submatrix_diagonal_equiv]
    rfl
  rw [← h1, h, map_mul, map_mul, h2]
  rfl

end Smith

section Blocks

variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)

abbrev blockOf : Fin n → Set.range β := Set.rangeFactorization β

abbrev Fiber (a : Set.range β) : Type := {i : Fin n // blockOf β i = a}

variable (R : Type*) [CommRing R]

def blockAssemble : (∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R) →+* Matrix (Fin n) (Fin n) R :=
  (reindexAlgEquiv R R (Equiv.sigmaFiberEquiv (blockOf β))).toRingEquiv.toRingHom.comp
    (blockDiagonal'RingHom (Fiber β) R)

def blocks (X : Matrix (Fin n) (Fin n) R) (a : Set.range β) : Matrix (Fiber β a) (Fiber β a) R :=
  fun i j => X i j

variable {β R}

theorem sigmaFiberEquiv_symm_eq {i : Fin n} {a : Set.range β} (hi : blockOf β i = a) :
    (Equiv.sigmaFiberEquiv (blockOf β)).symm i = ⟨a, ⟨i, hi⟩⟩ := by
  subst hi
  rfl

theorem blockAssemble_apply (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    (i j : Fin n) :
    blockAssemble β R X i j = blockDiagonal' X ((Equiv.sigmaFiberEquiv (blockOf β)).symm i)
      ((Equiv.sigmaFiberEquiv (blockOf β)).symm j) := rfl

theorem blockAssemble_apply_of_eq (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    {i j : Fin n} {a : Set.range β} (hi : blockOf β i = a) (hj : blockOf β j = a) :
    blockAssemble β R X i j = X a ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [blockAssemble_apply, sigmaFiberEquiv_symm_eq hi, sigmaFiberEquiv_symm_eq hj,
    blockDiagonal'_apply_eq]

theorem blockAssemble_apply_of_ne (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    {i j : Fin n} (h : β i ≠ β j) : blockAssemble β R X i j = 0 := by
  rw [blockAssemble_apply, sigmaFiberEquiv_symm_eq rfl, sigmaFiberEquiv_symm_eq rfl]
  exact blockDiagonal'_apply_ne _ _ _ fun e => h (congrArg Subtype.val e)

theorem blocks_blockAssemble (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R) :
    blocks β R (blockAssemble β R X) = X := by
  funext a
  ext i j
  exact blockAssemble_apply_of_eq X i.2 j.2

theorem blockAssemble_blocks {X : Matrix (Fin n) (Fin n) R}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) : blockAssemble β R (blocks β R X) = X := by
  ext i j
  by_cases h : β i = β j
  · have hj : blockOf β j = blockOf β i := Subtype.ext h.symm
    rw [blockAssemble_apply_of_eq _ rfl hj]
    rfl
  · rw [blockAssemble_apply_of_ne _ h, hX i j h]

theorem blockAssemble_diagonal (d : ∀ a : Set.range β, Fiber β a → R) :
    blockAssemble β R (fun a => diagonal (d a)) =
      diagonal fun i => d (blockOf β i) ⟨i, rfl⟩ := by
  ext i j
  by_cases h : β i = β j
  · have hj : blockOf β j = blockOf β i := Subtype.ext h.symm
    rw [blockAssemble_apply_of_eq _ rfl hj]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ (fun e => hij (congrArg Subtype.val e)), diagonal_apply_ne _ hij]
  · have hij : i ≠ j := fun e => h (by rw [e])
    rw [blockAssemble_apply_of_ne _ h, diagonal_apply_ne _ hij]

theorem blocks_mul {X Y : Matrix (Fin n) (Fin n) R} (hX : ∀ i j, β i ≠ β j → X i j = 0)
    (hY : ∀ i j, β i ≠ β j → Y i j = 0) :
    blocks β R (X * Y) = blocks β R X * blocks β R Y := by
  conv_lhs => rw [← blockAssemble_blocks hX, ← blockAssemble_blocks hY, ← map_mul]
  rw [blocks_blockAssemble]

end Blocks

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem exists_eq_mul_diagPow_mul_levi {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    ∃ μ : Fin n → ℤ, ∃ k₁ ∈ levi F n β ⊓ integralGL F n, ∃ k₂ ∈ levi F n β ⊓ integralGL F n,
      m = k₁ * Cartan.diagPow F n μ * k₂ := by
  classical
  have hϖ := Cartan.uniformizer_ne_zero F
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n (isCompact_singleton (x := m))
  have ht' : ∀ i j, (uniformizer F : F) ^ t * m i j ∈ 𝒪[F] := ht m rfl
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, ht' i j⟩
  have hAmap : A.map (𝒪[F]).subtype = (uniformizer F : F) ^ t • (m : Matrix (Fin n) (Fin n) F) := by
    ext i j
    rfl
  have hm0 : ∀ i j, β i ≠ β j → (m : Matrix (Fin n) (Fin n) F) i j = 0 := mem_levi.1 hm
  have hminv0 : ∀ i j, β i ≠ β j → ((m⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 :=
    mem_levi.1 ((levi F n β).inv_mem hm)
  have hA0 : ∀ i j, β i ≠ β j → A i j = 0 := by
    intro i j h
    apply Subtype.ext
    show (uniformizer F : F) ^ t * m i j = 0
    rw [hm0 i j h, mul_zero]

  have hblk : blocks β F (m : Matrix (Fin n) (Fin n) F) *
      blocks β F ((m⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← blocks_mul hm0 hminv0, Units.mul_inv]
    funext a
    ext i j
    show (1 : Matrix (Fin n) (Fin n) F) i.1 j.1 = (1 : Matrix (Fiber β a) (Fiber β a) F) i j
    by_cases hij : i = j
    · rw [hij, one_apply_eq, one_apply_eq]
    · rw [one_apply_ne hij, one_apply_ne (fun e => hij (Subtype.ext e))]
  have hdet : ∀ a, (blocks β 𝒪[F] A a).det ≠ 0 := by
    intro a h
    have h1 := congrArg (𝒪[F]).subtype h
    rw [map_zero, RingHom.map_det] at h1
    have h2 : (RingHom.mapMatrix (𝒪[F]).subtype) (blocks β 𝒪[F] A a) =
        (uniformizer F : F) ^ t • blocks β F (m : Matrix (Fin n) (Fin n) F) a := by
      ext i j
      rfl
    rw [h2, det_smul] at h1
    have h3 : (blocks β F (m : Matrix (Fin n) (Fin n) F) a) *
        (blocks β F ((m⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a) = 1 :=
      congrFun hblk a
    have h4 := congrArg Matrix.det h3
    rw [det_mul, det_one] at h4
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hϖ)) (left_ne_zero_of_mul_eq_one h4) h1
  choose P Q e hPQ using fun a => exists_eq_mul_diagonal_pow_mul_fintype
    (irreducible_uniformizer F) (blocks β 𝒪[F] A a) (hdet a)
  let Ψ := blockAssemble β 𝒪[F]
  let PU : GL (Fin n) 𝒪[F] := Units.map Ψ.toMonoidHom (MulEquiv.piUnits.symm P)
  let QU : GL (Fin n) 𝒪[F] := Units.map Ψ.toMonoidHom (MulEquiv.piUnits.symm Q)
  let e' : Fin n → ℕ := fun i => e (blockOf β i) ⟨i, rfl⟩
  have hAeq : A = (PU : Matrix (Fin n) (Fin n) 𝒪[F]) *
      diagonal (fun i => (GLnLocal.uniformizer F) ^ e' i) * (QU : Matrix (Fin n) (Fin n) 𝒪[F]) := by
    have hb : blocks β 𝒪[F] A = (fun a => (P a : Matrix _ _ 𝒪[F])) *
        (fun a => diagonal fun i => (GLnLocal.uniformizer F) ^ e a i) * (fun a => (Q a : Matrix _ _ 𝒪[F])) := by
      funext a
      exact hPQ a
    have hPU : (PU : Matrix (Fin n) (Fin n) 𝒪[F]) = Ψ (fun a => (P a : Matrix _ _ 𝒪[F])) := rfl
    have hQU : (QU : Matrix (Fin n) (Fin n) 𝒪[F]) = Ψ (fun a => (Q a : Matrix _ _ 𝒪[F])) := rfl
    rw [hPU, hQU, ← blockAssemble_blocks hA0, hb, map_mul, map_mul, blockAssemble_diagonal]
  have hlevi : ∀ U : GL (Fin n) 𝒪[F], (∀ i j, β i ≠ β j → (U : Matrix (Fin n) (Fin n) 𝒪[F]) i j = 0) →
      integralGLHom F n U ∈ levi F n β ⊓ integralGL F n := by
    intro U hU
    refine ⟨mem_levi.2 fun i j h => ?_, ⟨U, rfl⟩⟩
    rw [integralGLHom_apply, hU i j h]
    rfl
  refine ⟨fun i => (e' i : ℤ) - t, integralGLHom F n PU,
    hlevi PU fun i j h => blockAssemble_apply_of_ne _ h, integralGLHom F n QU,
    hlevi QU fun i j h => blockAssemble_apply_of_ne _ h, ?_⟩
  have key := congrArg (RingHom.mapMatrix (𝒪[F]).subtype) hAeq
  simp only [map_mul, RingHom.mapMatrix_apply] at key
  rw [hAmap, diagonal_map (map_zero _)] at key
  have hdiag : (diagonal fun i => ((𝒪[F]).subtype (GLnLocal.uniformizer F ^ e' i))) =
      (uniformizer F : F) ^ t • diagonal fun i => (uniformizer F : F) ^ ((e' i : ℤ) - t) := by
    ext i j
    rw [Matrix.smul_apply, diagonal_apply, diagonal_apply]
    split_ifs
    · rw [smul_eq_mul, map_pow, zpow_sub₀ hϖ, zpow_natCast, zpow_natCast,
        mul_div_cancel₀ _ (pow_ne_zero _ hϖ)]
      rfl
    · rw [smul_zero]
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul] at key
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Cartan.coe_diagPow]
  exact smul_right_injective _ (pow_ne_zero t hϖ) key

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.SphericalSatake
section
noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa Parabolic HeckeAlgebra AddMonoidAlgebra
open scoped ValuativeRel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem torusPow_add (l l' : Fin n → ℤ) :
    torusPow F n (l + l') = torusPow F n l * torusPow F n l' := by
  rw [torusPow, torusPow, torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem torusPow_zero : torusPow F n 0 = 1 := by
  rw [torusPow, ← map_one (diagGL F n)]
  congr 1
  funext i
  simp

theorem diagGL_mul_comm (a b : Fin n → Fˣ) : diagGL F n a * diagGL F n b = diagGL F n b * diagGL F n a := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem iwasawaExponent_one : iwasawaExponent F n (1 : GL (Fin n) F) = 0 := by
  simpa [torusPow_zero] using
    iwasawaExponent_eq F n (unipotent F n).one_mem (integralGL F n).one_mem (l := (0 : Fin n → ℤ))

theorem exists_diagGL_eq_torusPow_mul (d : Fin n → Fˣ) :
    ∃ l : Fin n → ℤ, ∃ e : Fin n → (𝒪[F])ˣ,
      diagGL F n d = torusPow F n l * diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i) := by
  choose l e he using fun i => exists_zpow_mul_unit F (d i).ne_zero
  refine ⟨l, e, ?_⟩
  rw [torusPow, ← map_mul]
  congr 1
  funext i
  ext
  simp [he i, Units.val_zpow_eq_zpow_val, Units.coe_map]

def diagUnits {b : GL (Fin n) F} (hb : b ∈ _root_.GroundTheory.Automorphic.Iwasawa.borel F n) : Fin n → Fˣ :=
  fun i => Units.mk0 (b i i) (apply_self_ne_zero_of_mem_borel F n hb i)

theorem mul_inv_diagUnits_mem_unipotent {b : GL (Fin n) F} (hb : b ∈ _root_.GroundTheory.Automorphic.Iwasawa.borel F n) :
    b * (diagGL F n (diagUnits hb))⁻¹ ∈ unipotent F n := by
  have hDinv : (diagGL F n (diagUnits hb))⁻¹ ∈ _root_.GroundTheory.Automorphic.Iwasawa.borel F n :=
    (_root_.GroundTheory.Automorphic.Iwasawa.borel F n).inv_mem (diagGL_mem_borel F n _)
  refine ⟨(_root_.GroundTheory.Automorphic.Iwasawa.borel F n).mul_mem hb hDinv, fun i => ?_⟩
  rw [mul_apply_self_of_mem_borel F n hb hDinv, ← map_inv, coe_diagGL, diagonal_apply_eq]
  simp [diagUnits, apply_self_ne_zero_of_mem_borel F n hb i]

theorem iwasawaExponent_mul_of_mem_borel {b : GL (Fin n) F} (hb : b ∈ _root_.GroundTheory.Automorphic.Iwasawa.borel F n)
    (g : GL (Fin n) F) :
    iwasawaExponent F n (b * g) = iwasawaExponent F n b + iwasawaExponent F n g := by
  obtain ⟨l, e, hde⟩ := exists_diagGL_eq_torusPow_mul (diagUnits hb)
  set D := diagGL F n (diagUnits hb)
  set E : GL (Fin n) F := diagGL F n fun i => Units.map (𝒪[F]).subtype.toMonoidHom (e i)
  have hE : E ∈ integralGL F n := diagGL_map_mem_integralGL F n e
  have hu := mul_inv_diagUnits_mem_unipotent hb
  have key : ∀ g : GL (Fin n) F, iwasawaExponent F n (b * g) = l + iwasawaExponent F n g := by
    intro g
    obtain ⟨u', hu', k', hk', hg⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
    set lg := iwasawaExponent F n g with hlg
    have hcomm : E * torusPow F n lg = torusPow F n lg * E :=
      diagGL_mul_comm _ _
    have hD : D⁻¹ * torusPow F n l = E⁻¹ := by
      rw [hde, _root_.mul_inv_rev, inv_mul_cancel_right]
    have : b * g = (b * D⁻¹ * (D * u' * D⁻¹)) * torusPow F n (l + lg) * (E * k') := by
      rw [torusPow_add]
      conv_lhs => rw [hg]
      calc b * (u' * torusPow F n lg * k')
          = b * u' * (E⁻¹ * (E * torusPow F n lg)) * k' := by group
        _ = b * u' * (E⁻¹ * (torusPow F n lg * E)) * k' := by rw [hcomm]
        _ = b * u' * ((D⁻¹ * torusPow F n l) * (torusPow F n lg * E)) * k' := by
            rw [hD]
        _ = _ := by group
    rw [this]
    refine iwasawaExponent_eq F n ((unipotent F n).mul_mem hu ?_) ((integralGL F n).mul_mem hE hk')
    exact diagGL_mul_mul_inv_mem_unipotent F n hu' _
  have hb1 := key 1
  rw [mul_one, iwasawaExponent_one, add_zero] at hb1
  rw [key, hb1]

def unramifiedChar (w : Fin n → ℂˣ) : levi F n (id : Fin n → Fin n) →* ℂ where
  toFun t := monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t)
  map_one' := by simp [iwasawaExponent_one]
  map_mul' t t' := by
    have ht : (t : GL (Fin n) F) ∈ _root_.GroundTheory.Automorphic.Iwasawa.borel F n := levi_le_blockUpper t.2
    simp only [Subgroup.coe_mul, iwasawaExponent_mul_of_mem_borel ht, monomialChar_add, map_mul]
    ring

theorem invSqrtModular_eq_one {p : blockUpper F n (id : Fin n → Fin n)}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : invSqrtModular F n id p = 1 := by
  have h := sqrtModular_mul_invSqrtModular p
  have hs : sqrtModular F n id p = 1 := by
    show ((NNReal.sqrt (Measure.modularCharacter p) : ℝ) : ℂ) = 1
    rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
    simp
  rwa [hs, one_mul] at h

theorem isUnramified_unramifiedChar (w : Fin n → ℂˣ) : IsUnramified (unramifiedChar (F := F) w) := by
  intro t ht
  show monomialChar (iwasawaExponent F n t) w * invSqrtModular F n id (leviIncl t) = 1
  have h0 : iwasawaExponent F n (t : GL (Fin n) F) = 0 := by
    simpa [iwasawaExponent_one] using iwasawaExponent_mul_of_mem_integralGL F n 1 ht
  rw [h0, monomialChar_zero, invSqrtModular_eq_one ht, one_mul]

theorem iwasawaExponent_leviProj (b : blockUpper F n (id : Fin n → Fin n)) :
    iwasawaExponent F n ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      iwasawaExponent F n (b : GL (Fin n) F) := by
  have hb : (b : GL (Fin n) F) ∈ _root_.GroundTheory.Automorphic.Iwasawa.borel F n := b.2
  have hD : ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F) =
      diagGL F n (diagUnits hb) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_diagGL, leviProj_apply]
    by_cases hij : i = j
    · subst hij
      simp [diagUnits]
    · simp [hij, diagonal_apply_ne _ hij]
  rw [hD]
  conv_rhs => rw [show (b : GL (Fin n) F) = (b * (diagGL F n (diagUnits hb))⁻¹) *
    diagGL F n (diagUnits hb) by group]
  rw [iwasawaExponent_mul_of_mem_unipotent F n (mul_inv_diagUnits_mem_unipotent hb)]

theorem borelChar_unramifiedChar (w : Fin n → ℂˣ) (b : blockUpper F n (id : Fin n → Fin n)) :
    borelChar (unramifiedChar w) b = monomialChar (iwasawaExponent F n (b : GL (Fin n) F)) w := by
  rw [borelChar_apply]
  change sqrtModular F n id b * (monomialChar (iwasawaExponent F n
    ((leviProj F n id b : levi F n (id : Fin n → Fin n)) : GL (Fin n) F)) w *
      invSqrtModular F n id (leviIncl (leviProj F n id b))) = _
  rw [iwasawaExponent_leviProj]
  have : invSqrtModular F n id (leviIncl (leviProj F n id b)) = invSqrtModular F n id b := by
    show (sqrtModular F n id (leviIncl (leviProj F n id b)))⁻¹ = (sqrtModular F n id b)⁻¹
    rw [sqrtModular_leviProj]
  rw [this, mul_left_comm, sqrtModular_mul_invSqrtModular, mul_one]

theorem sphericalFun_unramifiedChar (w : Fin n → ℂˣ) (g : GL (Fin n) F) :
    sphericalFun (unramifiedChar w) g = monomialChar (iwasawaExponent F n g) w := by
  obtain ⟨b, k, hk, rfl⟩ := exists_borel_mul g
  rw [sphericalFun_mul (isUnramified_unramifiedChar w) b hk, borelChar_unramifiedChar,
    iwasawaExponent_mul_of_mem_integralGL F n _ hk]


variable (F n) in
def integralOpen : OpenSubgroup (GL (Fin n) F) := ⟨integralGL F n, isOpen_integralGL F n⟩

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

def cosetSupport (h : SphericalHecke μ (F := F) (n := n)) :
    Finset (GL (Fin n) F ⧸ integralGL F n) :=
  (finite_image_mk_tsupport (integralOpen F n) (h : HeckeAlgebra μ).mem.2).toFinset

theorem apply_out_eq_zero {h : SphericalHecke μ (F := F) (n := n)}
    {x : GL (Fin n) F ⧸ integralGL F n} (hx : x ∉ cosetSupport h) :
    (h : HeckeAlgebra μ) x.out = 0 := by
  by_contra h0
  exact hx ((Set.Finite.mem_toFinset _).mpr ⟨x.out, subset_tsupport _ h0, QuotientGroup.out_eq' x⟩)

theorem sphericalEigen_unramifiedChar (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    sphericalEigen (unramifiedChar w) μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
      ∑ x ∈ cosetSupport h, (h : HeckeAlgebra μ) x.out *
        monomialChar (iwasawaExponent F n x.out) w := by
  have hf : HasCompactSupport fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g :=
    (h : HeckeAlgebra μ).mem.2.mul_right
  have hK : ∀ g, ∀ k ∈ integralOpen F n,
      (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) (g * k) =
        (fun g => (h : HeckeAlgebra μ) g * sphericalFun (unramifiedChar w) g) g := by
    intro g k hk
    simp only [sphericalFun_unramifiedChar, iwasawaExponent_mul_of_mem_integralGL F n g hk]
    rw [(HeckeAlgebraLevel.val_mem _ _ h k hk g).2]
  rw [sphericalEigen, integral_eq_smul_finsum_coset μ (integralOpen F n)
    (isCompact_integralGL F n) hf hK, Complex.real_smul]
  congr 1
  change (∑ᶠ x : GL (Fin n) F ⧸ integralGL F n,
    (h : HeckeAlgebra μ) x.out * sphericalFun (unramifiedChar w) x.out) = _
  rw [finsum_eq_sum_of_support_subset (s := cosetSupport h)]
  · simp only [sphericalFun_unramifiedChar]
  · intro x hx
    by_contra hxs
    exact hx (by simp [apply_out_eq_zero hxs])


variable (μ) in
def satake (h : SphericalHecke μ (F := F) (n := n)) : LaurentRing n :=
  (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
    ∑ x ∈ cosetSupport h, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out)

theorem satake_eq_sum (h : SphericalHecke μ (F := F) (n := n))
    (S : Finset (GL (Fin n) F ⧸ integralGL F n)) (hS : ∀ x ∉ S, (h : HeckeAlgebra μ) x.out = 0) :
    satake μ h = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ x ∈ S, single (iwasawaExponent F n x.out) ((h : HeckeAlgebra μ) x.out) := by
  classical
  rw [satake]
  congr 1
  rw [Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun x _ hx => by
      rw [apply_out_eq_zero hx, AddMonoidAlgebra.single_zero]]
  exact (Finset.sum_subset (Finset.subset_union_right (s₁ := cosetSupport h)) fun x _ hx => by
      rw [hS x hx, AddMonoidAlgebra.single_zero]).symm

theorem evalAt_satake (w : Fin n → ℂˣ) (h : SphericalHecke μ (F := F) (n := n)) :
    evalAt w (satake μ h) = sphericalCharacter μ (isUnramified_unramifiedChar w) h := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sphericalCharacter_apply, satake, map_smul, map_sum, sphericalEigen_unramifiedChar,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [evalAt_single]


variable (μ) in
def satakeHom : SphericalHecke μ (F := F) (n := n) →ₐ[ℂ] LaurentRing n where
  toFun := satake μ
  map_one' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_one]
  map_mul' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_mul]
  map_zero' := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_zero]
  map_add' a b := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, map_add (f := _)]
  commutes' c := eq_of_forall_evalAt fun w => by simp only [evalAt_satake, AlgHom.commutes]

theorem satakeHom_apply (h : SphericalHecke μ (F := F) (n := n)) : satakeHom μ h = satake μ h := rfl

theorem evalAt_comp_satakeHom (w : Fin n → ℂˣ) :
    (evalAt w).comp (satakeHom μ) = sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w) :=
  AlgHom.ext fun h => evalAt_satake w h

end Spherical

end GroundTheory.Automorphic
end
end

