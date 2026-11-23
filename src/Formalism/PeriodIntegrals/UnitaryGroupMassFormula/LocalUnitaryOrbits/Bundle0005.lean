module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfIdxV
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

abbrev latA : AddSubgroup (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v Λ).toAddSubgroup

def lattice₂ (ϖ : Fv F v) : AddSubgroup (Fin n → Fv F v ⊗[F] E) :=
  (latA v Λ).map (DistribSMul.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))

def IdxV (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n)

def redT (a : ℕ) (ϖ : Fv F v) :
    lamA v Λ a →+ (Fin a → latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) where
  toFun X i := QuotientAddGroup.mk ⟨(X : TupV (E := E) v n a) i, X.2 i⟩
  map_zero' := by
    funext i
    rw [Pi.zero_apply, ← QuotientAddGroup.mk_zero]
    rfl
  map_add' X Y := by
    funext i
    rw [Pi.add_apply, ← QuotientAddGroup.mk_add]
    rfl

theorem redT_surj (a : ℕ) (ϖ : Fv F v) : Function.Surjective (redT v Λ a ϖ) := by
  intro c
  refine ⟨⟨fun i => ((c i).out : Fin n → Fv F v ⊗[F] E), fun i => (c i).out.2⟩, ?_⟩
  funext i
  show QuotientAddGroup.mk ⟨((c i).out : Fin n → Fv F v ⊗[F] E), (c i).out.2⟩ = c i
  exact QuotientAddGroup.out_eq' (c i)

theorem redT_ker (a : ℕ) (ϖ : Fv F v) :
    (redT v Λ a ϖ).ker = (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a) := by
  ext X
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    have hi : ∀ i, ∃ z ∈ latLoc (E := E) v Λ, sc (E := E) v ϖ • z = (X : TupV (E := E) v n a) i := by
      intro i
      have h1 := congrFun h i
      change (QuotientAddGroup.mk _ : latA v Λ ⧸ _) = 0 at h1
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
      obtain ⟨z, hz, hze⟩ := h1
      exact ⟨z, hz, hze⟩
    choose Z hZ hZe using hi
    exact ⟨Z, hZ, funext hZe⟩
  · rintro ⟨Z, hZ, hZe⟩
    funext i
    change (QuotientAddGroup.mk _ : latA v Λ ⧸ _) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨Z i, hZ i, congrFun hZe i⟩

theorem idxU_of (a : ℕ) (Y : TupV (E := E) v n a) (h : IdxV σ J ψ v Λ a Y) : IdxU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hV := h hG ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsIntSmulMemAll
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
  PI.VolStabSW PI.VolStabSW.PositiveNearLattice PI.VolStabSW.SdDualW
open scoped TensorProduct

section TopWs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem sdc_exists_int_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem exists_int_smul_mem_all (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) {ι : Type} [Fintype ι] (w : ι → Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ j, y • w j ∈ L := by
  classical
  choose y hy hw using fun j => sdc_exists_int_smul_mem L hL (w j)
  refine ⟨∏ j, y j, Finset.prod_ne_zero_iff.2 fun j _ => hy j, fun j => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul]
  exact zsmul_mem (hw j) _

theorem ratV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem ratV_mem_latLoc {Λ : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ Λ) :
    ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v Λ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem sdc_isOpen_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsOpen (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  obtain ⟨d, b, hb⟩ := exists_int_basis (F := F) (E := E)
  letI : Submodule.IsFullLattice E L := hLat
  obtain ⟨N, hN, hNw⟩ := exists_int_smul_mem_all L
    (Submodule.IsFullLattice.span_eq_top (A := E) (M := L))
    (fun p : Fin n × Fin d => (Pi.single p.1 (b p.2) : Fin n → E))
  have hNF : IsUnit ((N : F)) := by
    rw [isUnit_iff_ne_zero]
    exact_mod_cast hN
  set b2 := b.isUnitSMul (fun _ => hNF) with hb2
  have hb2L : ∀ i k, (Pi.single i (b2 k) : Fin n → E) ∈ L := by
    intro i k
    have e : (Pi.single i (b2 k) : Fin n → E) = N • (Pi.single i (b k) : Fin n → E) := by
      rw [hb2, Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
      funext j
      by_cases h : j = i
      · subst h
        simp
      · simp [Pi.single_eq_of_ne h]
    rw [e]
    exact hNw (i, k)
  let H : AddSubgroup (Fin n → Fv F v ⊗[F] E) := AddSubgroup.pi Set.univ (fun _ => latA v b2)
  have hHo : IsOpen (H : Set (Fin n → Fv F v ⊗[F] E)) := by
    rw [AddSubgroup.coe_pi]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_latA v b2
  have hle : H ≤ (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup := by
    intro X hX
    rw [AddSubgroup.mem_pi] at hX
    rw [Submodule.mem_toAddSubgroup, ← Finset.univ_sum_single X]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hXi : ∀ k, crd b2 (Fv F v) (X i) k ∈ v.adicCompletionIntegers F := hX i (Set.mem_univ _)
    have e : Pi.single i (X i) = ∑ k, crd b2 (Fv F v) (X i) k •
        ratV (F := F) (Fv F v) (Pi.single i (b2 k) : Fin n → E) := by
      have hr := (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr (X i)
      simp only [Algebra.TensorProduct.basis_apply] at hr
      funext j
      by_cases h : j = i
      · subst h
        simp only [ratV_single, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
        conv_lhs => rw [← hr]
        rfl
      · simp [ratV_single, Finset.sum_apply, Pi.single_eq_of_ne h]
    rw [e]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ (⟨_, hXi k⟩ : v.adicCompletionIntegers F) (ratV_mem_latLoc v (hb2L i k))
  exact AddSubgroup.isOpen_mono hle hHo

theorem sdc_isCompact_latLoc (Λ : Set (Fin n → E))
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) :
    IsCompact (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hLat, rfl⟩ := hL
  have : Module.Finite (𝓞 E) L := Submodule.IsLattice.finite (A := E) L
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  set g : Fin m → Fin n → Fv F v ⊗[F] E := fun i => ratV (F := F) (Fv F v) ((s i : L) : Fin n → E)
    with hg
  have hadd : ∀ p q : Fin n → E, ratV (F := F) (Fv F v) (p + q) =
      ratV (F := F) (Fv F v) p + ratV (F := F) (Fv F v) q := by
    intro p q
    funext j
    simp [ratV]
  have hzs : ∀ (r : ℤ) (p : Fin n → E), ratV (F := F) (Fv F v) (r • p) = r • ratV (F := F) (Fv F v) p := by
    intro r p
    funext j
    simp [ratV]
  have e : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      (fun c : Fin m → Fv F v => ∑ i, c i • g i) ''
        Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext z
    constructor
    · intro hz
      have h1 : z ∈ Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
        refine (Submodule.span_le.2 ?_) hz
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact Submodule.mem_top
        have key : ∀ y : L, y ∈ Submodule.span ℤ (Set.range s) →
            ratV (F := F) (Fv F v) (y : Fin n → E) ∈
              Submodule.span (v.adicCompletionIntegers F) (Set.range g) := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨i, rfl⟩ := hy
            exact Submodule.subset_span ⟨i, rfl⟩
          | zero =>
            have : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
              funext j
              simp [ratV]
            simpa [this] using Submodule.zero_mem _
          | add p q _ _ hp hq =>
            rw [Submodule.coe_add, hadd]
            exact Submodule.add_mem _ hp hq
          | smul r p _ hp =>
            rw [show ((r • p : L) : Fin n → E) = r • (p : Fin n → E) from rfl, hzs]
            exact zsmul_mem hp r
        exact key _ hx'
      rw [Submodule.mem_span_range_iff_exists_fun] at h1
      obtain ⟨c, rfl⟩ := h1
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ (⟨c i, hc i (Set.mem_univ _)⟩ : v.adicCompletionIntegers F)
          (ratV_mem_latLoc v (s i).2)
  rw [e]
  exact (isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image
    (continuous_finsetSum _ fun i _ => by fun_prop)

theorem topW_holds (Λ : Set (Fin n → E)) (a : ℕ)
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ) : TopW v Λ a := by
  intro hL
  have e : LamT (E := E) v Λ a =
      Set.pi Set.univ (fun _ : Fin a => (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E))) := by
    ext X
    simp [LamT, Set.mem_pi]
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => sdc_isCompact_latLoc v Λ hL,
    isOpen_set_pi Set.finite_univ fun _ _ => sdc_isOpen_latLoc v Λ hFull⟩

end TopWs

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddRight
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

abbrev OR : Subring (Fv F v ⊗[F] E) := Orb.oRing (E := E) v (Orb.oSub (E := E) v)

def IsRes (ϖ : Fv F v) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) : Prop :=
  Function.Surjective π ∧ (∀ x : OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ) ∧
    ∀ x y : OR (E := E) v, (y : Fv F v ⊗[F] E) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x → π y = τ (π x)

theorem hR_add_right (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + z) = hR (Fv F v) σ J x y + hR (Fv F v) σ J x z := by
  simp only [hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem coord_eq (e : Fin n → Fin n → Fv F v ⊗[F] E) (he1 : gramR (Fv F v) σ J e = 1)
    (c : Fin n → Fv F v ⊗[F] E) (j : Fin n) : hR (Fv F v) σ J (e j) (∑ i, c i • e i) = c j := by
  rw [Orb.hR_sum_right σ J v]
  have h : ∀ i, hR (Fv F v) σ J (e j) (e i) = (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) j i := by
    intro i; rw [← he1]; rfl
  simp only [h, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem bas_mem {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (j : Fin n) :
    e j ∈ latLoc (E := E) v Λ := by
  refine (he _).2 ⟨Pi.single j 1, fun i => ?_, ?_⟩
  · by_cases h : i = j
    · subst h; simpa using (Orb.oSub (E := E) v).1
    · simpa [Pi.single_apply, h] using Orb.oev_zero (E := E) v
  · simp [Pi.single_apply, ite_smul]

theorem expand {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) :
    x = ∑ j, hR (Fv F v) σ J (e j) x • e j := by
  obtain ⟨c, -, rfl⟩ := (he x).1 hx
  simp only [coord_eq σ J v e he1]

theorem ffGram_one {K : Type} [CommRing K] (τ : K →+* K) {a : ℕ} (X : Fin a → Fin n → K) (i j : Fin a) :
    ffGram τ (1 : Matrix (Fin n) (Fin n) K) X i j = ∑ p, τ (X i p) * X j p := by
  simp only [ffGram, ffH, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem gY_mem {a : ℕ} {Y : TupV (E := E) v n a} (hG : GoodY σ J ψ v Λ a Y) (i j : Fin a) :
    gramR (Fv F v) σ J Y i j ∈ OR (E := E) v :=
  (hG.2.2.1 (Y j)).1 (hG.2.2.2.2.2.1.1 j) (Y i) (hG.2.2.2.2.2.1.1 i)

end PI.OmLocU.Red
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem oEv_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v :=
  (PI.OmLocU.Orb.oSub (E := E) v).2 x hx y hy

theorem oEv_sum {ι : Type} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ i ∈ s, f i ∈ OEv (E := E) v) :
    ∑ i ∈ s, f i ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.sum_mem _ h

theorem hR_sum_smul_right {a : ℕ} (x : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (y : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ k, c k • y k) = ∑ k, c k * hR (Fv F v) σ J x (y k) := by
  have := map_sum (PI.VolStabSW.hLin (Fv F v) σ J x) (fun k => c k • y k) Finset.univ
  simp only [map_smul, smul_eq_mul] at this
  exact this

theorem hR_smul_left' (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_smul_left {a : ℕ} (y : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (x : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (∑ k, c k • x k) y = ∑ k, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (c k) * hR (Fv F v) σ J (x k) y := by
  have := map_sum (AddMonoidHom.mk' (fun z => hR (Fv F v) σ J z y) (fun z z' => hR_add_left σ J z z' y))
    (fun k => c k • x k) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun k _ => hR_smul_left' σ J v (c k) (x k) y

section Onto

variable (Λ : Set (Fin n → E)) (ψ : AddChar (AF F) ℂ)

def GramInvO (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ y ∈ LamT v Λ a,
    (∀ i j, gramR (Fv F v) σ J y i j - gramR (Fv F v) σ J Y i j ∈ PO (E := E) v ϖ) →
    ∃ Ginv : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), (∀ i j, Ginv i j ∈ OEv (E := E) v) ∧
      gramR (Fv F v) σ J y * Ginv = 1

def TrOnto : Prop :=
  UnramAt (E := E) v → ∀ s ∈ OEv (E := E) v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ s = s →
    ∃ x ∈ OEv (E := E) v, x + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x = s

theorem hensOnto_of (a : ℕ) (Y : TupV (E := E) v n a) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v) :
    HensOnto σ J v Λ ψ a Y := by
  classical
  intro hGood ϖ hϖ y hy hyT S hS
  obtain ⟨Ginv, hGi, hGG⟩ := hGI hGood ϖ hϖ y hy hyT
  obtain ⟨L, -, hLΛ⟩ := hGood.2.1
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hGood.1.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hGood.1.2.1.1
  have hdiag : ∀ i, ∃ x ∈ OEv (E := E) v, x + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x = (S : Matrix (Fin a) (Fin a) _) i i :=
    fun i => hTr hGood.2.2.2.1 _ (hS i i) (S.2 i i)
  choose x hx hxs using hdiag
  set A : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then (S : Matrix (Fin a) (Fin a) _) i j else if i = j then x i else 0 with hAdef
  have hA : ∀ i j, A i j ∈ OEv (E := E) v := by
    intro i j
    simp only [hAdef]
    split_ifs
    · exact hS i j
    · exact hx i
    · exact oEv_zero v
  have hAS : ∀ i j, A i j + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (A j i) = (S : Matrix (Fin a) (Fin a) _) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hAdef, h, not_lt.2 h.le, h.ne']
    · simp [hAdef, hxs]
    · simp only [hAdef, h, not_lt.2 h.le, h.ne, h.ne', if_false, if_true, zero_add]
      exact S.2 i j
  set C := Ginv * A with hCdef
  have hC : ∀ i j, C i j ∈ OEv (E := E) v := fun i j => by
    rw [hCdef, Matrix.mul_apply]
    exact oEv_sum v _ _ fun k _ => oEv_mul v (hGi i k) (hA k j)
  have hGm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ y
  subst hLΛ
  refine ⟨fun j => ∑ k, C k j • y k, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => oEv_smul_mem v L (hC k j) (hy k)
  · funext i j
    simp only [crossM]
    rw [hR_sum_smul_right, hR_sum_smul_left]
    have e1 : ∑ k, C k j * hR (Fv F v) σ J (y i) (y k) = A i j := by
      have : (gramR (Fv F v) σ J y * C) i j = A i j := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      rw [← this, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have e2 : ∑ k, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (C k i) * hR (Fv F v) σ J (y k) (y j) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (A j i) := by
      have : (gramR (Fv F v) σ J y * C) j i = A j i := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← this, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, mul_comm]
      congr 1
      exact (hGm k j).symm
    rw [e1, e2, hAS]

end Onto

end PI.OmLocU
end
end

