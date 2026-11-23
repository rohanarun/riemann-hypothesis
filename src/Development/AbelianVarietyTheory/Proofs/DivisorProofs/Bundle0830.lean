module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PicGlue

theorem stalkMap_gm {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem rigOn_of_triv_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X),
    (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  intro X Y e V L hV ⟨t, ht⟩
  have hle : ∀ a : L.ι, e ⁻¹ᵁ L.U a ≤ V.ι ''ᵁ (L.pull (V.ι ≫ e)).U (fun _ => a) := by
    intro a y hy
    obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y hy
    exact V.ι.apply_mem_image_iff.2 (mem_pull.2 hy)
  refine ⟨fun a => res (hle a) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => a)), ?_⟩
  intro y a b ha hb
  obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y ha
  have key : ∀ c : L.ι, e (V.ι v) ∈ L.U c →
      gm V.ι v (e ⁻¹ᵁ L.U c) (res (hle c) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => c))) =
        gm (𝟙 V.toScheme) v _ (t.s fun _ => c) := by
    intro c hc
    have hm : (𝟙 V.toScheme) v ∈ (L.pull (V.ι ≫ e)).U (fun _ => c) := mem_pull.2 hc
    rw [gm_res V.ι v (hle c) (show V.ι v ∈ e ⁻¹ᵁ L.U c from hc)]
    have := GlobalTheory.GlueLineBundle.gm_imU V.ι (𝟙 V.toScheme) v _ hm (t.s fun _ => c)
    rwa [Category.id_comp] at this
  have hinj : Function.Injective (Units.map (V.ι.stalkMap v).hom.toMonoidHom) :=
    Units.map_injective (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.injective
  apply hinj
  rw [map_mul, stalkMap_gm, stalkMap_gm, stalkMap_gm, Category.comp_id]
  beta_reduce
  rw [key a ha, key b hb,
    (isGen_iff_germ t).1 ht v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    gm_pull_g L (V.ι ≫ e) (𝟙 V.toScheme) v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    Category.id_comp]

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOrderPiMatrixEmbeddings
section
noncomputable section

namespace GlobalTheory.UPel.HT.SplitC

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix TensorProduct
open GlobalTheory.UPel.HT

theorem span_embeddings_eq_top (K : Type) [Field K] [NumberField K] :
    Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) = ⊤ := by
  rw [eq_top_iff, ← (canonicalEmbedding.latticeBasis K).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨RingOfIntegers.basis K i, ?_⟩
  rw [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rfl

theorem mem_of_embeddings {K : Type} [Field K] [NumberField K] {W : Type} [AddCommGroup W] [Module ℂ W]
    (V : Submodule ℂ W) (L : ((K →+* ℂ) → ℂ) → W) (hadd : ∀ f g, L (f + g) = L f + L g)
    (hsmul : ∀ (a : ℂ) f, L (a • f) = a • L f) (h : ∀ c : 𝓞 K, L (fun τ => τ (c : K)) ∈ V)
    (f : (K →+* ℂ) → ℂ) : L f ∈ V := by
  let Ll : ((K →+* ℂ) → ℂ) →ₗ[ℂ] W := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  have hf : f ∈ Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) := by
    rw [span_embeddings_eq_top]; trivial
  have : Ll f ∈ (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll :=
    Submodule.mem_map_of_mem hf
  have hle : (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll ≤ V := by
    rw [Submodule.map_span_le]
    rintro _ ⟨c, rfl⟩
    exact h c
  exact hle this

variable {p : ℕ} [Fact p.Prime]

def padicToComplex (j : PadicAlgCl p ≃+* ℂ) : ℤ_[p] →+* ℂ :=
  j.toRingHom.comp ((algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom)

def evalTensor (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) : 𝓞 F ⊗[ℤ] ℤ_[p] →+* ℂ :=
  (Algebra.TensorProduct.lift (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom κ.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem evalTensor_tmul (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) (c : 𝓞 F) (z : ℤ_[p]) :
    evalTensor F κ τ (c ⊗ₜ z) = τ (c : F) * κ z := by
  simp [evalTensor]

def bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) :
    (D.O ⊗[ℤ] ℤ_[p]) →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) :=
  Pi.ringHom fun τ => (evalTensor D.F κ τ).mapMatrix.comp e.toRingHom

theorem bigPhi_algebraMap (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (c : 𝓞 D.F) (τ : D.F →+* ℂ) :
    bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) τ = Matrix.scalar (Fin D.m) (τ (c : D.F)) := by
  have h1 : (algebraMap (𝓞 D.F) D.O c ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c := rfl
  rw [h1]
  show (evalTensor D.F κ τ).mapMatrix (e (algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c)) = _
  rw [e.commutes c, Matrix.algebraMap_eq_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.scalar_apply, Algebra.TensorProduct.algebraMap_apply, evalTensor_tmul]
  split_ifs <;> simp [evalTensor_tmul]

theorem tmul_one_comm {A : Type} [Ring A] (z : ℤ_[p]) (a : A ⊗[ℤ] ℤ_[p]) :
    a * ((1 : A) ⊗ₜ z) = ((1 : A) ⊗ₜ z) * a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

theorem bigPhi_one_tmul (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (z : ℤ_[p]) :
    ∃ w : 𝓞 D.F ⊗[ℤ] ℤ_[p], bigPhi D κ e ((1 : D.O) ⊗ₜ z) = fun τ => Matrix.scalar (Fin D.m) (evalTensor D.F κ τ w) := by
  have hc : e ((1 : D.O) ⊗ₜ z) ∈ Set.center (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    rw [Semigroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tmul_one_comm]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨w, funext fun τ => ?_⟩
  show (evalTensor D.F κ τ).mapMatrix (e ((1 : D.O) ⊗ₜ z)) = _
  rw [← hw]
  ext i j
  simp only [Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem mem_span_bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (y : D.O ⊗[ℤ] ℤ_[p]) :
    bigPhi D κ e y ∈ Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom)) := by
  set V := Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom))
  have hφ : ∀ x : D.O, bigPhi D κ e (x ⊗ₜ 1) ∈ V := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hL : ∀ (x : D.O) (f : (D.F →+* ℂ) → ℂ),
      (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1) ∈ V := by
    intro x
    apply mem_of_embeddings V (fun f => (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1))
    · intro f g
      funext τ
      simp only [Pi.mul_apply, Pi.add_apply, map_add (f := _), _root_.add_mul]
    · intro a f
      funext τ
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_mul, _root_.mul_assoc]
    · intro c
      have : (fun τ : D.F →+* ℂ => Matrix.scalar (Fin D.m) (τ (c : D.F))) =
          bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) := funext fun τ => (bigPhi_algebraMap D κ e c τ).symm
      rw [this, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
      exact hφ _
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    obtain ⟨w, hw⟩ := bigPhi_one_tmul D κ e z
    have : x ⊗ₜ[ℤ] z = ((1 : D.O) ⊗ₜ z) * (x ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
    rw [this, map_mul, hw]
    exact hL x _
  | add a b ha hb => rw [map_add (f := _)]; exact V.add_mem ha hb

theorem bigPhi_symm_single (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (i j : Fin D.m) (c : 𝓞 D.F) :
    bigPhi D κ e (e.symm (Matrix.single i j (c ⊗ₜ 1))) = fun τ => Matrix.single i j (τ (c : D.F)) := by
  funext τ
  show (evalTensor D.F κ τ).mapMatrix (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [evalTensor_tmul]

theorem exists_ringHom_pi_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p),
    ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ),
      (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧
        Submodule.span ℂ (Set.range φ) = ⊤ := by
  intro p _ D
  obtain ⟨e⟩ := D.splitP
  obtain ⟨j⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  set κ := padicToComplex j
  refine ⟨(bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom, fun c τ => bigPhi_algebraMap D κ e c τ, ?_⟩
  rw [eq_top_iff]
  intro X _
  have hX : X = ∑ i, ∑ k, (fun τ => Matrix.single i k (X τ i k)) := by
    funext τ
    simp only [Finset.sum_apply]
    exact Matrix.matrix_eq_sum_single (X τ)
  rw [hX]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => ?_
  apply mem_of_embeddings _ (fun f => fun τ => Matrix.single i k (f τ)) (f := fun τ => X τ i k)
  · intro f g; funext τ; simp [Matrix.single_add]
  · intro a f; funext τ; simp [Matrix.smul_single]
  · intro c
    rw [← bigPhi_symm_single D κ e i k c]
    exact mem_span_bigPhi D κ e _

end GlobalTheory.UPel.HT.SplitC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserIdeleMultiplicativeOnIdeals
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt UniqueFactorizationMonoid

namespace GlobalTheory.CMVal.IdealIdele

variable {E : Type} [Field E] [NumberField E]


open Classical in
def primeIdele (p : Ideal (𝓞 E)) : (Af E)ˣ :=
  if h : p.IsPrime ∧ p ≠ ⊥ then unifAt ⟨p, h.1, h.2⟩ else 1

def idl (I : Ideal (𝓞 E)) : (Af E)ˣ := ((normalizedFactors I).map primeIdele).prod

theorem idl_top : idl (⊤ : Ideal (𝓞 E)) = 1 := by
  rw [idl, ← Ideal.one_eq_top, normalizedFactors_one]; simp

theorem idl_mul {I J : Ideal (𝓞 E)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : idl (I * J) = idl I * idl J := by
  rw [idl, normalizedFactors_mul hI hJ, Multiset.map_add (f := _), Multiset.prod_add]; rfl

theorem nf_prime (v : HeightOneSpectrum (𝓞 E)) : normalizedFactors v.asIdeal = {v.asIdeal} := by
  rw [normalizedFactors_irreducible v.irreducible, normalize_eq]

theorem idl_prime (v : HeightOneSpectrum (𝓞 E)) : idl v.asIdeal = unifAt v := by
  rw [idl, nf_prime, Multiset.map_singleton, Multiset.prod_singleton, primeIdele,
    dite_eq_left ⟨v.isPrime, v.ne_bot⟩]

theorem ind {P : Ideal (𝓞 E) → Prop} (h1 : P ⊤)
    (h2 : ∀ (v : HeightOneSpectrum (𝓞 E)) (I : Ideal (𝓞 E)), I ≠ ⊥ → P I → P (v.asIdeal * I)) :
    ∀ I, I ≠ ⊥ → P I := fun I => by
  refine induction_on_prime (P := fun I => I ≠ ⊥ → P I) I (fun h => absurd rfl h) ?_ ?_
  · intro x hx _
    rw [Ideal.isUnit_iff.1 hx]; exact h1
  · intro a p ha hp h _
    exact h2 ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ a ha (h ha)

theorem mul_apply' (a b : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl

theorem one_apply' (w : HeightOneSpectrum (𝓞 E)) : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl

theorem modF_idl : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → modF (idl I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹ := by
  refine ind ?_ ?_
  · rw [idl_top, modF_eq_one fun w => by rw [one_apply', map_one]]
    simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, ObjModel.modF_mul, h, idl_prime, modF_unifAt, map_mul]
    push_cast
    rw [mul_inv]

open Classical in
theorem val_idl (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    Valued.v ((idl I : Af E) w) = WithZero.exp (-((normalizedFactors I).count w.asIdeal : ℤ)) := by
  refine ind ?_ ?_
  · rw [idl_top, one_apply', map_one, ← Ideal.one_eq_top, normalizedFactors_one]; simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, mul_apply', map_mul, h, idl_prime, normalizedFactors_mul v.ne_bot hI, nf_prime,
      Multiset.count_add]
    by_cases hw : w = v
    · subst hw
      rw [(unifAt_spec w).2, ← WithZero.exp_add, Multiset.count_singleton_self]
      congr 1; push_cast; ring
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      rw [(unifAt_spec v).1 w hw, map_one, one_mul, Multiset.count_singleton, if_neg this, zero_add]

theorem idl_eq_one (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    ¬ w.asIdeal ∣ I → (idl I : Af E) w = 1 := by
  refine ind ?_ ?_
  · intro _; rw [idl_top, one_apply']
  · intro v I hI h hd
    have hw : w ≠ v := by
      rintro rfl
      exact hd (dvd_mul_right _ _)
    rw [idl_mul v.ne_bot hI, mul_apply', h fun h => hd (h.mul_left _), idl_prime, (unifAt_spec v).1 w hw, one_mul]

theorem mem_nf {w : HeightOneSpectrum (𝓞 E)} {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (h : w.asIdeal ∣ I) :
    w.asIdeal ∈ normalizedFactors I :=
  (mem_normalizedFactors_iff hI).2 ⟨w.prime, h⟩

open Classical in
theorem exists_count (n : HeightOneSpectrum (𝓞 E) → ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ I : Ideal (𝓞 E), I ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 E),
      (normalizedFactors I).count w.asIdeal = if w ∈ S then n w else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun w => by rw [normalizedFactors_one]; simp⟩
  | insert v S hv ih =>
    obtain ⟨I, hI, h⟩ := ih
    have h0 : v.asIdeal ^ n v ≠ 0 := pow_ne_zero _ v.ne_bot
    refine ⟨v.asIdeal ^ n v * I, mul_ne_zero h0 hI, fun w => ?_⟩
    rw [normalizedFactors_mul h0 hI, normalizedFactors_pow, nf_prime, Multiset.count_add, h, Multiset.count_nsmul,
      Multiset.count_singleton]
    by_cases hw : w = v
    · subst hw; simp [hv]
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      simp [this, hw]

theorem finite_val_ne_one (z : (Af E)ˣ) : {w : HeightOneSpectrum (𝓞 E) | Valued.v ((z : Af E) w) ≠ 1}.Finite :=
  GlobalTheory.Mem.TupHecke.finite_nonunit z

theorem main : ∀ (E : Type) [Field E] [NumberField E], ∃ t : Ideal (𝓞 E) → (Af E)ˣ, t ⊤ = 1 ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → t (I * J) = t I * t J) ∧ (∀ v : HeightOneSpectrum (𝓞 E), t v.asIdeal = unifAt v) ∧
    (∀ I, I ≠ ⊥ → modF (t I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ∧
    (∀ I, I ≠ ⊥ → ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((t I : Af E) w) ≤ 1 ∧
      (w.asIdeal ∣ I → Valued.v ((t I : Af E) w) < 1) ∧ (¬ w.asIdeal ∣ I → (t I : Af E) w = 1)) ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → (∀ w, Valued.v ((t I : Af E) w) = Valued.v ((t J : Af E) w)) → I = J) ∧
    ∀ z : (Af E)ˣ, (∀ w, Valued.v ((z : Af E) w) ≤ 1) →
      ∃ I, I ≠ ⊥ ∧ ∀ w, Valued.v ((t I : Af E) w) = Valued.v ((z : Af E) w) := by
  intro E _ _
  classical
  refine ⟨idl, idl_top, fun _ _ => idl_mul, idl_prime, modF_idl, fun I hI w => ⟨?_, fun hd => ?_, idl_eq_one w I hI⟩,
    fun I J hI hJ h => ?_, fun z hz => ?_⟩
  · rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · have := Multiset.count_pos.2 (mem_nf hI hd)
    rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  · have e : normalizedFactors I = normalizedFactors J := by
      ext p
      by_cases hp : Prime p
      · have := h ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
        rw [val_idl _ I hI, val_idl _ J hJ, WithZero.exp_inj] at this
        simpa using this
      · rw [Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h),
          Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h)]
    rw [← Ideal.prod_normalizedFactors_eq_self hI, e, Ideal.prod_normalizedFactors_eq_self hJ]
  · obtain ⟨I, hI, h⟩ := exists_count (fun w => (-(Valued.v ((z : Af E) w)).log).toNat)
      (finite_val_ne_one z).toFinset
    refine ⟨I, hI, fun w => ?_⟩
    rw [val_idl w I hI, h]
    split_ifs with hw
    · have h0 := ObjModel.coord_ne z w
      have h1 : (Valued.v ((z : Af E) w)).log ≤ 0 := by
        rw [← WithZero.exp_le_exp, WithZero.exp_log h0]; exact hz w
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
    · have : Valued.v ((z : Af E) w) = 1 := by simpa using hw
      rw [this]; simp

end GlobalTheory.CMVal.IdealIdele
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilChange

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaO_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := {
  quasi γ w := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi]
    ring
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul, h u hu h0]⟩
  cont := hf.cont.const_smul c
  smooth k L hL h0 w := (hf.smooth k L hL h0 w).const_smul c }

theorem triv_of_resEta_zero {ν : (AE D)ˣ →* Circle} (h : ResEta D ν 0) (a : (AF D.host.F)ˣ) : ν (idF D a) = 1 := by
  obtain ⟨η, hη⟩ := h.1
  rw [h.2 η hη a, pow_zero]

theorem hecke_mul {χ ν : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hν : IsHeckeChar D ν) : IsHeckeChar D (χ * ν) :=
  ⟨hχ.1.mul hν.1, fun x => by rw [MonoidHom.mul_apply, hχ.2, hν.2, mul_one]⟩

theorem hecke_inv {ν : (AE D)ˣ →* Circle} (hν : IsHeckeChar D ν) : IsHeckeChar D ν⁻¹ :=
  ⟨hν.1.inv, fun x => by rw [MonoidHom.inv_apply, hν.2, inv_one]⟩

theorem exists_weilDatum_twist : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (νS νT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsHeckeChar D νS → IsHeckeChar D νT → ResEta D νS 0 → ResEta D νT 0 → ∃ om', IsWeilDatumO ψ S T (χS * νS) (χT * νT) om' ∧ ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → om' (g, h) = ((((νT x)⁻¹ * νS y : Circle) : ℂ)) • om (g, h) := by
  intro D ψ hψ S T χS χT νS νT om ho hS hT rS rT
  obtain ⟨a, aval, amul, anorm, arat, acont⟩ :=
    GlobalTheory.Member.exists_muVal D S νT⁻¹ (hecke_inv hT) (triv_of_resEta_zero (resEta_inv rT))
  obtain ⟨b, bval, bmul, bnorm, brat, bcont⟩ := GlobalTheory.Member.exists_muVal D T νS hS (triv_of_resEta_zero rS)
  have a1 : a 1 = 1 := arat 1 (one_mem _)
  have b1 : b 1 = 1 := brat 1 (one_mem _)
  let om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ) :=
    { toFun := fun p => (a p.1 * b p.2) • om p
      map_one' := by rw [Prod.fst_one, Prod.snd_one, a1, b1, map_one, one_mul, one_smul]
      map_mul' := fun p q => by
        rw [Prod.fst_mul, Prod.snd_mul, amul, bmul, map_mul, smul_mul_smul_comm, mul_mul_mul_comm] }
  have happ : ∀ p f, om' p f = (a p.1 * b p.2) • om p f := fun p f => rfl
  have hval : ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y →
      a g * b h = (((νT x)⁻¹ * νS y : Circle) : ℂ) := by
    intro g h x y hx hy
    rw [aval.2 g x hx, bval.2 h y hy, Circle.coe_mul, MonoidHom.inv_apply]
  refine ⟨om', ⟨hψ, hecke_mul ho.hecS hS, hecke_mul ho.hecT hT, resEta_mul ho.resS rS, resEta_mul ho.resT rT,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p f hf
    rw [happ]
    exact thetaO_smul _ (ho.om_pres p f hf)
  · intro g h w₀ f hf
    rw [happ, happ, heisO_smul, ho.om_heis g h w₀ f hf]
  · intro γ hγ γ' hγ' f hf
    rw [happ, arat γ hγ, brat γ' hγ', one_mul, one_smul]
    exact ho.om_aut γ hγ γ' hγ' f hf
  · intro f hf w
    exact ((acont.comp continuous_fst).mul (bcont.comp continuous_snd)).mul (ho.om_cont f hf w)
  · intro μ 𝓕 hμ h𝓕 p f hf
    rw [← ho.om_unit μ 𝓕 hμ h𝓕 p f hf]
    refine lintegral_congr fun w => ?_
    have hn : ‖om' p f w‖ = ‖om p f w‖ := by
      rw [happ, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, anorm, bnorm, one_mul, one_mul]
    rw [← ofReal_norm, ← ofReal_norm, hn]
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := ho.om_split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [happ, map_smul, H ℓ hℓ f hf,
      hval g h x y (isDetAt_root he S g hg x hx) (isDetAt_root he T h hh y hy)]
    simp only [splitFacO, MonoidHom.mul_apply, mul_inv, Circle.coe_mul, smul_eq_mul]
    ring
  · intro g h x y hx hy
    rw [← hval g h x y hx hy]
    rfl

end GlobalTheory.WeilChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosetsStatement
section
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets : ∀ {H : Type} [Group H] (a : H → ℂ), (Function.support a).Finite → ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  first | exact @GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | exact GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | (intros; apply GlobalTheory.ConjRegroup.finsum_eq_finsum_classes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_translate_ratio_global_unit : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio  <;> assumption)
end

