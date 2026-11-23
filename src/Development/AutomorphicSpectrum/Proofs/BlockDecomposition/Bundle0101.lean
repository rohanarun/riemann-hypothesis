module

public import Mathlib
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdditiveCharacterSumOrthogonality
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.Orth

theorem sum_inv_addChar_mul_left (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : K) :
    (∑ t : K, (ψ₀ (t * x))⁻¹) = if x = 0 then (Fintype.card K : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    have hbij : Function.Bijective (fun t : K => -(t * x)) := by
      refine ⟨fun a b h => ?_, fun b => ⟨-(b * x⁻¹), ?_⟩⟩
      · exact mul_right_cancel₀ hx (neg_injective h)
      · simp [hx]
    have h1 : (∑ t : K, (ψ₀ (t * x))⁻¹) = ∑ t : K, ψ₀ (-(t * x)) :=
      Finset.sum_congr rfl fun t _ => (AddChar.map_neg_eq_inv ψ₀ (t * x)).symm
    rw [h1, hbij.sum_comp (fun u => ψ₀ u)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem sum_inv_addChar_dot (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : Fin j → K) :
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹)
      = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  have h1 : ∀ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹ = ∏ i, (ψ₀ (r i * x i))⁻¹ := by
    intro r
    have hs : ∀ s : Finset (Fin j), ψ₀ (∑ i ∈ s, r i * x i) = ∏ i ∈ s, ψ₀ (r i * x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    rw [hs, Finset.prod_inv_distrib]
  have h2 : (∑ r : Fin j → K, ∏ i, (ψ₀ (r i * x i))⁻¹)
      = ∏ i, ∑ t : K, (ψ₀ (t * x i))⁻¹ := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1]
  rw [h2]
  simp_rw [sum_inv_addChar_mul_left K ψ₀ hψ]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem orth : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ),
    ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 :=
  fun K _ _ _ j ψ₀ hψ x => sum_inv_addChar_dot K j ψ₀ hψ x

end GlobalTheory.CompanionTheory.TyFin.Orth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockEmbeddingGLInverse
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL

variable (K : Type) [Field K]

theorem sum_fin_of_ge_zero {d j : ℕ} (hjd : j ≤ d) (f : Fin d → K)
    (hf : ∀ k : Fin d, j ≤ (k : ℕ) → f k = 0) :
    ∑ k, f k = ∑ k : Fin j, f (Fin.castLE hjd k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjd
  rw [Fin.sum_univ_add]
  have h0 : ∑ k : Fin m, f (Fin.natAdd j k) = 0 :=
    Finset.sum_eq_zero fun k _ => hf _ (by simp)
  rw [h0, add_zero]
  rfl

theorem blkEmb_row_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : j ≤ (i : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dite_eq_right fun h => (not_lt.2 hi) h.1]

theorem blkEmb_col_ge {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hl : j ≤ (l : ℕ)) : blkEmb K d j A i l = if i = l then 1 else 0 := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dite_eq_right fun h => (not_lt.2 hl) h.2]

theorem blkEmb_lt {d j : ℕ} (A : Matrix (Fin j) (Fin j) K) (i l : Fin d)
    (hi : (i : ℕ) < j) (hl : (l : ℕ) < j) :
    blkEmb K d j A i l = A ⟨i, hi⟩ ⟨l, hl⟩ := by
  simp only [GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb]
  rw [dite_eq_left ⟨hi, hl⟩]

theorem blkEmb_one (d j : ℕ) : blkEmb K d j (1 : Matrix (Fin j) (Fin j) K) = 1 := by
  ext i l
  rw [Matrix.one_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.one_apply]
      simp [Fin.ext_iff]
    · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l (not_lt.1 hl)
  · exact GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l (not_lt.1 hi)

theorem blkEmb_mul {d j : ℕ} (hjd : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) :
    blkEmb K d j (A * B) = blkEmb K d j A * blkEmb K d j B := by
  ext i l
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < j
  · by_cases hl : (l : ℕ) < j
    · rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i l hi hl, Matrix.mul_apply,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.sum_fin_of_ge_zero K hjd]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hk : ((Fin.castLE hjd k : Fin d) : ℕ) < j := k.2
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ i _ hi hk,
          GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_lt K _ _ l hk hl]
        rfl
      · intro k hk
        rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i k hk, if_neg (by rintro rfl; omega),
          zero_mul]
    · have hl' : j ≤ (l : ℕ) := not_lt.1 hl
      rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K _ i l hl']
      simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K B _ l hl', mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_col_ge K A i l hl']
  · have hi' : j ≤ (i : ℕ) := not_lt.1 hi
    rw [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K _ i l hi']
    simp only [GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K A i _ hi', ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_row_ge K B i l hi']

theorem exists_gl_blkEmb : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ), j ≤ d →
    ∀ g : GL (Fin j) K, ∃ h : GL (Fin d) K,
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) ∧
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
  intro K _ _ _ d j hjd g
  refine ⟨⟨GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j (g : Matrix (Fin j) (Fin j) K),
    GlobalTheory.CompanionTheory.TyFin.ColStep.blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K), ?_, ?_⟩, rfl, rfl⟩
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]
  · rw [← GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_mul K hjd, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL.blkEmb_one]

end GlobalTheory.CompanionTheory.TyFin.BlockEmbeddingGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmpPutSucc
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open GlobalTheory.CatH (face toLast)
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def ev (r : ℕ) (T : D) : Ψ.Pr T →+ F.obj T where
  toFun x := (x r).1
  map_zero' := rfl
  map_add' _ _ := rfl

def cmp (r j : ℕ) (f : Cn Ψ.rees j) : Cn F j := fun s => ev Ψ r _ (f s)

def cmpS (r j : ℕ) (f : Cn Ψ.rees j) : Cn (Ψ.S r).fn j := fun s => (show Ψ.Pr _ from f s) r

def put (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from fun r => match r with
    | 0 => ⟨z s, by rw [h0]; trivial⟩
    | _ + 1 => 0

theorem cmp_d (r j : ℕ) (f : Cn Ψ.rees j) : cmp Ψ r (j + 1) (d Ψ.rees j f) = d F j (cmp Ψ r j f) := by
  funext s
  refine (map_sum (ev Ψ r _) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_zsmul]
  rfl

theorem cmp_zero (r j : ℕ) : cmp Ψ r j 0 = 0 := rfl

theorem cmp_sub (r j : ℕ) (f g : Cn Ψ.rees j) : cmp Ψ r j (f - g) = cmp Ψ r j f - cmp Ψ r j g := rfl

theorem cmp_put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : cmp Ψ 0 j (put Ψ h0 j z) = z := rfl

theorem cmp_put_succ (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (r j : ℕ) (z : Cn F j) : cmp Ψ (r + 1) j (put Ψ h0 j z) = 0 := rfl

theorem cochain_ext {j : ℕ} {f g : Cn Ψ.rees j} (h : ∀ r, cmp Ψ r j f = cmp Ψ r j g) : f = g := by
  funext s
  refine funext fun r => Subtype.ext ?_
  exact congrFun (h r) s

theorem put_d (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    d Ψ.rees j (put Ψ h0 j z) = put Ψ h0 (j + 1) (d F j z) := by
  refine cochain_ext Ψ fun r => ?_
  rw [cmp_d]
  cases r with
  | zero => rfl
  | succ r =>
    rw [cmp_put_succ, cmp_put_succ, map_zero]

theorem put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) : put Ψ h0 j 0 = 0 := by
  refine cochain_ext Ψ fun r => ?_
  cases r <;> rfl

theorem cmp_X (j r : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + 1) j ((X : ℤ[X]) • f) = Ψ.μ • cmp Ψ r j f := by
  funext s
  exact Ψ.X_smul_succ _ (f s) r

theorem cmp_X_pow (j k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ k j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ 0 j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, cmp_X, ih, pow_succ', mul_smul]

theorem cmp_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmp Ψ r j a ∈ (cx F).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmp Ψ r j e, (cmp_d Ψ r j e).symm⟩

theorem put_mem_B (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (a : Cn F j) (h : a ∈ (cx F).B j) :
    put Ψ h0 j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, put_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨put Ψ h0 j e, put_d Ψ h0 j e⟩

theorem d_cmpS (r j : ℕ) (f : Cn Ψ.rees j) (hf : d Ψ.rees j f = 0) : d (Ψ.S r).fn j (cmpS Ψ r j f) = 0 := by
  funext s
  refine Subtype.ext ?_
  have h1 := congrFun ((Ψ.S r).inc.d_pullC j (cmpS Ψ r j f)) s
  have h2 : d F j (cmp Ψ r j f) = 0 := by rw [← cmp_d, hf, cmp_zero]
  exact h1.symm.trans (congrFun h2 s)

end

end GlobalTheory.CompanionTheory.ReesDown

namespace GlobalTheory.CompanionTheory.ReesDown

theorem put_pull {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (h0 : ∀ T, (Φ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    (Mor.restrict Φ.rees G).pullC j (put Φ h0 j z) =
      put (Φ.comap G) (fun T => h0 (G.obj T)) j ((Mor.restrict F G).pullC j z) := by
  refine cochain_ext (Φ.comap G) fun r => ?_
  cases r <;> rfl

theorem main : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y := by
  intro R _ C _ C' _ F Φ G n N h0 hRI j hj
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  have hpd : ∀ (z : Cn F j), d F j z = 0 → d (G ⋙ F) j ((Mor.restrict F G).pullC j z) = 0 := fun z hz => by
    rw [Mor.d_pullC, hz, map_zero]
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx F) j).1 x
    have h2 : (Mor.restrict F G).pullC j z ∈ (cx (G ⋙ F)).B j := by
      have h1 := P.mapH_cls (Mor.restrict F G).hom j z hz (hpd z hz)
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.1 _ _).1 (h1.symm.trans hx)
    have hZ : d Φ.rees j (put Φ h0 j z) = 0 := by
      rw [put_d, hz]; exact put_zero Φ h0 _
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (put Φ h0 j z)) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 := by
      refine (P.mapH_cls (Mor.restrict Φ.rees G).hom j _ hZ hZ').trans ?_
      refine ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ _).2 ?_
      have key : ∀ a : (cx (G ⋙ Φ.rees)).X j, a = put (Φ.comap G) h0' j ((Mor.restrict F G).pullC j z) →
          a ∈ (cx (G ⋙ Φ.rees)).B j := by
        intro a ha
        subst ha
        exact put_mem_B (Φ.comap G) h0' j _ h2
      exact key _ (put_pull Φ G h0 j z)
    have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • put Φ h0 j z) = 0 := by
      rw [map_smul, hZ, smul_zero]
    have h4 := hU.1 _ h3
    rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
    have h5 := cmp_mem_B Φ N j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
    rw [cmp_X_pow, cmp_put_zero] at h5
    have hμ : d F j (Φ.μ ^ N • z) = 0 := by rw [map_smul, hz, smul_zero]
    rw [← (P.cls_surj (cx F) j).2.2.2.2 _ _ hz hμ]
    exact ((P.cls_surj (cx F) j).2.1 _ hμ).2 h5
  · obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
    have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
      refine (put_d (Φ.comap G) h0' j w).trans ?_
      rw [hw]; exact put_zero (Φ.comap G) h0' _
    obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
    obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
      rw [map_smul, hW, smul_zero]
    have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
    rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
    have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
    have hc : (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w ∈ (cx (G ⋙ F)).B j := by
      have h := cmp_mem_B (Φ.comap G) N j _ hB
      have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
          cmp (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
            (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w := by
        intro A hA
        rw [cmp_sub, cmp_X_pow, cmp_put_zero, hA]
        rfl
      exact (e _ rfl) ▸ h
    have hz0 : d F j (cmp Φ N j Z) = 0 := by rw [← cmp_d, hZ, cmp_zero]
    have hμ : d (G ⋙ F) j (Φ.μ ^ N • w) = 0 := by rw [map_smul, hw, smul_zero]
    refine ⟨(cx F).cls _ hz0, ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ?_⟩, ?_⟩
    · exact P.mapH_cls (Φ.S N).inc.hom j _ _ hz0
    · refine (P.mapH_cls (Mor.restrict F G).hom j _ hz0 (hpd _ hz0)).trans ?_
      rw [← (P.cls_surj (cx (G ⋙ F)) j).2.2.2.2 _ _ hw hμ]
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.2.1 _ _ _ hμ).2 hc

end GlobalTheory.CompanionTheory.ReesDown
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupAssocC
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CupAssocC

section
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

theorem term_term (F : C ⥤ ModuleCat.{w} R) {p m n : ℕ} (s : ComposableArrows C n) (f : Cn F p)
    (g : Fin (m + 1) → Fin (n + 1)) (hg : Monotone g) (g' : Fin (p + 1) → Fin (m + 1)) (hg' : Monotone g') :
    (F.map (s.map (homOfLE (Fin.le_last (g (Fin.last m)))))).hom (term F (hg.functor ⋙ s) f g' hg') =
      term F s f (g ∘ g') (hg.comp hg') := by
  have e : (hg.functor ⋙ s).map (homOfLE (Fin.le_last (g' (Fin.last p)))) ≫
      s.map (homOfLE (Fin.le_last (g (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (g (g' (Fin.last p))))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  have key : ∀ {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (x : F.obj X),
      (F.map b).hom ((F.map a).hom x) = (F.map (a ≫ b)).hom x := by
    intro X Y Z a b x
    rw [F.map_comp]; rfl
  refine (key _ _ _).trans ?_
  exact congrArg (fun φ => (F.map φ).hom (f ((hg.comp hg').functor ⋙ s))) e

theorem term_id (F : C ⥤ ModuleCat.{w} R) {n : ℕ} (s : ComposableArrows C n) (f : Cn F n) :
    term F s f id monotone_id = f s := by
  have e : s.map (homOfLE (Fin.le_last (id (Fin.last n)))) = 𝟙 _ := by
    rw [← s.map_id]; rfl
  unfold term
  rw [e, F.map_id]
  rfl

theorem term_cupC {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q a n : ℕ} (h : p + q = a) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) (θ : Fin (a + 1) → Fin (n + 1)) (hθ : Monotone θ) :
    term F₃ s (P.cupC h f g) θ hθ =
      P.μ _ (term F₁ s f (θ ∘ front h) (hθ.comp (front_mono h)))
        (term F₂ s g (θ ∘ back h) (hθ.comp (back_mono h))) := by
  rw [← term_term F₁ s f θ hθ _ (front_mono h), ← term_term F₂ s g θ hθ _ (back_mono h), P.nat]
  rfl

theorem cupC_at {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C ⥤ ModuleCat.{w'} R} {F₃ : C ⥤ ModuleCat.{w''} R}
    (P : Pairing F₁ F₂ F₃) {p q n : ℕ} (h : p + q = n) (f : Cn F₁ p) (g : Cn F₂ q)
    (s : ComposableArrows C n) :
    P.cupC h f g s = P.μ _ (term F₁ s f (front h) (front_mono h)) (term F₂ s g (back h) (back_mono h)) := rfl

theorem term_one (A : C ⥤ CommAlgCat.{w} R) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin (0 + 1) → Fin (n + 1)) (hg : Monotone g) :
    term (modF A) s (fun s => (1 : A.obj (s.obj (Fin.last 0)))) g hg = (1 : A.obj (s.obj (Fin.last n))) :=
  map_one (A.map (s.map (homOfLE (Fin.le_last (g (Fin.last 0)))))).hom

end

theorem cup_assocC : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (A : C ⥤ CommAlgCat.{w} R), (∀ n (x : Cn (modF A) n), (mulP A).cupC (Nat.zero_add n) (fun s => (1 : A.obj (s.obj (Fin.last 0)))) x = x ∧ (mulP A).cupC (Nat.add_zero n) x (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = x) ∧ ∀ {p q r a b n : ℕ} (h₁ : p + q = a) (h₂ : a + r = n) (h₃ : q + r = b) (h₄ : p + b = n) x y z, (mulP A).cupC h₂ ((mulP A).cupC h₁ x y) z = (mulP A).cupC h₄ x ((mulP A).cupC h₃ y z) := by
  intro R _ C _ A
  refine ⟨fun n x => ⟨?_, ?_⟩, ?_⟩
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (back_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [back])), term_id]
    exact one_mul (M := A.obj (s.obj (Fin.last n))) _
  · funext s
    rw [cupC_at, term_one, term_congr (modF A) s x (front_mono _) monotone_id
      (funext fun i => Fin.ext (by simp [front])), term_id]
    exact mul_one (M := A.obj (s.obj (Fin.last n))) _
  · intro p q r a b n h₁ h₂ h₃ h₄ x y z
    funext s
    rw [cupC_at, cupC_at, term_cupC, term_cupC,
      term_congr (modF A) s x ((front_mono h₂).comp (front_mono h₁)) (front_mono h₄)
        (funext fun i => Fin.ext (by simp [front])),
      term_congr (modF A) s y ((front_mono h₂).comp (back_mono h₁)) ((back_mono h₄).comp (front_mono h₃))
        (funext fun i => Fin.ext (by simp [front, back])),
      term_congr (modF A) s z (back_mono h₂) ((back_mono h₄).comp (back_mono h₃))
        (funext fun i => Fin.ext (by simp [back]; omega))]
    exact mul_assoc (G := A.obj (s.obj (Fin.last n))) _ _ _

end GlobalTheory.CompanionTheory.CupAssocC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ElementsBijectiveOfBijectiveApp
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.Cech

theorem elMor_bijective_of_bijective {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {E' E : C ⥤ Type t} (p : E' ⟶ E) (F : C ⥤ ModuleCat.{w} R) (h : ∀ T, Function.Bijective (p.app T)) (n : ℕ) : Function.Bijective ((elMor p F).hom.f n) := by
  haveI : ∀ T, IsIso (p.app T) := fun T => (isIso_iff_bijective _).2 (h T)
  haveI : IsIso p := NatIso.isIso_of_isIso_app p
  have e1 : ∀ x, (elMor (inv p) F).pullC n ((elMor p F).pullC n x) = x := fun x => by
    have e : (inv p ≫ p : E ⟶ E) = 𝟙 E := IsIso.inv_hom_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  have e2 : ∀ x, (elMor p F).pullC n ((elMor (inv p) F).pullC n x) = x := fun x => by
    have e : (p ≫ inv p : E' ⟶ E') = 𝟙 E' := IsIso.hom_inv_id p
    exact congrArg (fun a => (elMor a F).pullC n x) e
  exact Function.bijective_iff_has_inverse.2 ⟨(elMor (inv p) F).pullC n, e1, e2⟩

end GlobalTheory.CompanionTheory.Cech
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDegreeOnePrimeNotSplitsCompletely
section
open NumberField IsDedekindDomain GroundTheory.Global

namespace GlobalTheory.CompanionTheory.Density


open Filter _root_.Topology Set in
theorem exists_degreeOnePrime_not_splitsCompletely :
    ∀ (L F M : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], 1 < Module.finrank F M →
      ∀ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite →
        ∃ v ∈ degreeOnePrimes L F, v ∉ B ∧ ¬ SplitsCompletely M v := by
  intro L F M _ _ _ _ _ _ _ _ _ hdeg B hB
  by_contra hcon
  push Not at hcon
  have hfin : (degreeOnePrimes L F \ ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩ degreeOnePrimes L F)).Finite := by
    apply hB.subset
    intro v hv
    by_contra hvB
    exact hv.2 ⟨hcon v hv.1 hvB, hv.1⟩
  have hinter : ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩
      degreeOnePrimes L F).HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_iff_of_subset_of_isBoundedUnder
      Set.inter_subset_right
      (GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite hfin) 1).mpr
      (GroundTheory.Global.hasDirichletDensity_degreeOnePrimes (K := L) (L := F))
  have hsplit : {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}.HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff
      (K := L) _ 1).mp hinter
  have hSd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely (K := F) (L := M)
  have heq : (1 : ℝ) = 1 / Module.finrank F M :=
    hsplit.dirichletDensity_eq.symm.trans hSd.dirichletDensity_eq
  have h2 : 2 ≤ Module.finrank F M := hdeg
  have hfr : (2 : ℝ) ≤ Module.finrank F M := by exact_mod_cast h2
  have hq : (1 : ℝ) / Module.finrank F M ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfr
  linarith

end GlobalTheory.CompanionTheory.Density
end

