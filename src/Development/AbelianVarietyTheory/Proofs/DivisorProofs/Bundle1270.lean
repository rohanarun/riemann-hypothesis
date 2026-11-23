module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0889
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormHeightEqHt
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeightTieProof

theorem formHeight_eq_ht {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) :
    formHeight δ w A f = ht w A f + (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2 := by
  have hr : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold ht formHeight
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
  field_simp
  ring

theorem ht_pow (hM : HtMul) {F : Type} [Field F] [NumberField F] {B N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} {Λ : ℝ} (hL : Lat w A Λ) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous a f) (e : ℕ) :
    ht w A (f ^ e) = e * ht w A f := by
  induction e with
  | zero =>
    have := (hM F B N n w A Λ hL).2 1 one_ne_zero
    simpa using this
  | succ k ih =>
    have hk : IsMultiHomogeneous (k • a) (f ^ k) :=
      isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 ha).pow k)
    rw [pow_succ, (hM F B N n w A Λ hL).1 (k • a) a _ _ (pow_ne_zero k hf) hf hk ha, ih]
    push_cast; ring

theorem heightTie : HtMul → HeightTie := by
  intro hM F _ _ T Λ hL h hh d e f c hf he hc
  obtain ⟨d', f', -, hf', e'⟩ := hh
  obtain ⟨rfl, c', hc', rfl⟩ := hf.isChowFormInt.unique hf'.isChowFormInt
  have hf0 := hf.isChowFormInt.ne_zero
  have hd := hf.isChowFormInt.pos
  rw [HeightUnique.formHeight_C_mul hL.pos d hL.spans hL.det hf0 hf.homog hc', formHeight_eq_ht] at e'
  have hpow : IsMultiHomogeneous (e • fun _ => d) (f ^ e) :=
    isMultiHomogeneous_iff_block.2 ((isMultiHomogeneous_iff_block.1 hf.homog).pow e)
  have key : ht T.w T.A (C c * f ^ e) = e * ht T.w T.A f := by
    unfold ht
    rw [HeightUnique.formHeight_C_mul hL.pos 0 hL.spans hL.det (pow_ne_zero e hf0) hpow hc]
    exact ht_pow hM hL hf0 hf.homog e
  have hD : (0 : ℝ) < (T.D : ℝ) + 1 := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have eq1 : ht T.w T.A (C c * f ^ e) / (((T.D : ℝ) + 1) * (e * d : ℕ)) =
      h - (harmonic (T.N - 1) : ℝ) / 2 := by
    rw [key, div_eq_iff (by push_cast; positivity)]
    push_cast
    push_cast at e'
    have : ht T.w T.A f = ((T.D : ℝ) + 1) * d * h - ((T.D : ℝ) + 1) * d * (harmonic (T.N - 1) : ℝ) / 2 := by
      linarith
    rw [this]; ring
  refine ⟨eq1, ?_⟩
  rw [eq1]

  have hNn : T.N ≤ T.n := by
    have h1 := finrank_range_le_card (R := F) (b := T.w.col)
    rw [Set.finrank, hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hH : (harmonic (T.N - 1) : ℝ) ≤ 1 + Real.log (T.N - 1 : ℕ) := harmonic_le_one_add_log _
  have hlog : Real.log (T.N - 1 : ℕ) ≤ Real.log T.n := by
    rcases Nat.eq_zero_or_pos (T.N - 1) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : T.N - 1 ≤ T.n))
  linarith

end GlobalTheory.HeightTieProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem frame_mul_map (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) L) (Y : Matrix (Fin m) (Fin k) L) :
    ((1 - ι 1) • (1 : Matrix (Fin m) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι) * Y.map ι = (A * Y).map ι := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
    zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, hmul]

theorem map_mul_frame_transpose (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {m k : ℕ}
    (C : Matrix (Fin k) (Fin k) L) (Y : Matrix (Fin m) (Fin k) L) :
    Y.map ι * ((1 - ι 1) • (1 : Matrix (Fin k) (Fin k) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι)ᵀ = (Y * Cᵀ).map ι := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sub_mul, one_mul, ← hmul, one_mul, sub_self,
    zero_add, Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
  simp only [Matrix.map_apply, Matrix.transpose_apply, hmul]

theorem actAB_xm_frame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (PV : GL (Fin n) L) (PW : GL (Fin d) L) (A : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin d) (Fin d) L)
    (g : UA σ X.J) (h : UA σ W.J)
    (hg : mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι)
    (hh : mat h = (1 - ι 1) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + C.map ι) (x : Matrix (Fin d) (Fin n) L) :
    actAB (cA σ) (g, h) (xm ι PV PW x) =
      (A * (PV : Matrix (Fin n) (Fin n) L) * xᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ * Cᵀ).map ι := by
  change mat g * xm ι PV PW x * (mat h)ᵀ = _
  rw [xm_apply, hg, hh, frame_mul_map ι hmul, map_mul_frame_transpose ι hmul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.InertLocFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HadamardIneqComplexCombinationsBasis
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
open Matrix
open scoped ComplexOrder ComplexConjugate

namespace GlobalTheory.HSShort

theorem hadamard_basis_comb : ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V)
    (d : ℕ) (b : Module.Basis (Fin d) F V) (σ : F →+* ℂ) (P : Matrix (Fin d) (Fin d) ℂ),
    0 < (nm.gram σ b).det.re ∧
      ‖P.det‖ * Real.sqrt (nm.gram σ b).det.re ≤ ∏ k, cnrm nm σ (fun i => P i k) b := by
  intro F V _ _ _ nm d b σ P
  have hG : (nm.gram σ b).PosDef := nm.posDef σ d b b.linearIndependent
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hG.det_pos
  refine ⟨hre, ?_⟩
  set G := nm.gram σ b with hGdef
  have hM : (Pᴴ * G * P).PosSemidef := hG.posSemidef.conjTranspose_mul_mul_same P
  have h1 := ReciprocityTheory.ChartRestriction.G.T0.psd_det_re_le_prod_diag d _ hM
  have hdet : (Pᴴ * G * P).det.re = ‖P.det‖ ^ 2 * G.det.re := by
    rw [det_mul, det_mul, det_conjTranspose]
    have : star P.det * G.det * P.det = ((Complex.normSq P.det : ℝ) : ℂ) * G.det := by
      rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]; ring
    rw [this, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  have hdiag : ∀ k, ((Pᴴ * G * P) k k).re = csq nm σ (fun i => P i k) b := by
    intro k
    simp only [csq, Matrix.mul_apply, Matrix.conjTranspose_apply, hGdef, HermFam.gram, Matrix.of_apply,
      Finset.sum_mul, Complex.star_def]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdet] at h1
  simp only [hdiag] at h1
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ csq nm σ (fun i => P i k) b := fun k _ => csq_nonneg nm σ _ _
  calc ‖P.det‖ * Real.sqrt G.det.re = Real.sqrt (‖P.det‖ ^ 2 * G.det.re) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∏ k, csq nm σ (fun i => P i k) b) := Real.sqrt_le_sqrt h1
    _ = ∏ k, cnrm nm σ (fun i => P i k) b := by
        rw [Real.sqrt_prod _ hnn]; rfl

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliWithSymplecticLevelRepresentab
section
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def IsLevelStructureOfLevel {D : Datum F} {p N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (N₁ : ℕ)
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  (∀ a c, α (a + c) = α a * α c) ∧ (∀ a, α (N₁ • a) = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      (∀ a, toUnit (Over.mk x) ≫ α a = 1 ↔ ∃ b, a = N₁ • b) ∧
      (∀ g : Over.mk x ⟶ o.A, g ^ N₁ = 1 → ∃ a, toUnit _ ≫ α a = g) ∧
      ∃ z : kˣ, IsPrimitiveRoot z N₁ ∧
        ∀ a b, Out.WeilIs o.A o.PP.L N₁ (toUnit (Over.mk x) ≫ α a) (toUnit _ ≫ α b) (unitOn (z ^ D.EF a b))

def LevelStructurePullback {D : Datum F} {p N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp (D.OEp p)} {s' : S' ⟶ Sp (D.OEp p)}
    {o' : Obj D p N s'} {o : Obj D p N s} {f : S' ⟶ S} (m : ObjMap o' o f) (α' : D.La → (𝟙_ (Over S') ⟶ o'.A))
    (α : D.La → (𝟙_ (Over S) ⟶ o.A)) : Prop :=
  ∀ a, (α' a).left ≫ m.φ = f ≫ (α a).left

def HasLevelStructureOfLevel {D : Datum F} {p N : ℕ} {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp (D.OEp p)} (o₁ : Obj D p N s₁) (N₁ : ℕ)
    (α₁ : D.La → (𝟙_ (Over X₁) ⟶ o₁.A)) : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp (D.OEp p)) (o : Obj D p N s) (α : D.La → (𝟙_ (Over S) ⟶ o.A)), IsLevelStructureOfLevel o N₁ α →
    ∃! f : S ⟶ X₁, f ≫ s₁ = s ∧ ∃ m : ObjMap o o₁ f, LevelStructurePullback m α α₁

end GlobalTheory.UPel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HatCPhiHat
section
open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.WeilParts GlobalTheory.AdTh
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh

theorem unr_of {D : D7} {χ : (AE D)ˣ →* Circle} (h : UnramEverywhere D χ) {v ε} (hε : IsPlaceIdem D v ε) : UnramAt ε χ := by
  intro x hx h1 h2
  refine h x ?_ h1 h2
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem hatC_phiHat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {n : ℕ} (φ : (Fin n → LevQc Dw l) → c.F) (hf : Finite (Fin n → LevQc Dw l)) (q : Fin n → LevQ Dw l) :
    hatC l (fun x => (φ x : ℂ)) q = ((phiHat c φ q : c.F) : ℂ) := by
  have hz : ((zetaM c : c.F) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) := by
    have hM : (l.M : ℂ) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
    have hM' : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by rintro rfl; simp at hk; exact hM' hk : k ≠ 0)
    simp only [zetaM, SubmonoidClass.coe_pow, zeta]
    rw [← Complex.exp_nat_mul, hk, Nat.mul_div_cancel_left _ (by have := l.three_le; omega)]
    congr 1; push_cast; field_simp
  have := Fintype.ofFinite (Fin n → LevQc Dw l)
  unfold hatC phiHat
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← hz]
  show _ = c.F.val _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_zpow₀]
  rfl

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePolynomials_of_carried_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  first | exact @GlobalTheory.CarriedHecke.hecke_polys_of_carries | exact GlobalTheory.CarriedHecke.hecke_polys_of_carries | (intros; apply GlobalTheory.CarriedHecke.hecke_polys_of_carries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeRel
section
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

structure IntSim (D : Datum F) (p : ℕ) where
  c : ℕ
  k : ℕ
  c_cop : c.Coprime p
  k_cop : k.Coprime p
  g : ℕ → D.La →ₗ[𝓞 F] D.La
  compat : ∀ n m : ℕ, (n * m).Coprime p → ∀ a, ∃ b, g (n * m) a - g n a = n • b
  sim : ∀ n : ℕ, n.Coprime p → ∃ u : ℤ, IsCoprime u (n : ℤ) ∧
    ∀ a b, (n : ℤ) ∣ D.EF (g n a) (g n b) - c * u * D.EF a b
  onto : ∀ n : ℕ, n.Coprime p → ∀ a, ∃ b d, g n b = k • a + n • d

namespace IntSim

variable {D : Datum F} {p : ℕ}

end IntSim

variable {S : Scheme.{0}}

def HeckeRel {D : Datum F} {p N N' : ℕ} (g : IntSim D p) {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s)
    (o' : Obj D p N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ Etale ψ.left ∧
    (∀ x, o'.eta x = o.eta ((N' / (N * g.k)) • g.g N' x) ≫ ψ) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (t : Over.mk x ⟶ o.A),
      t ≫ ψ = 1 ↔ ∃ a, t = toUnit _ ≫ o.eta ((N' / g.k) • g.g N' a)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → n.Coprime p →
      ∀ (P Q : Over.mk x ⟶ o.A), P ^ n = 1 → Q ^ n = 1 → ∀ ζ : kˣ,
        Out.WeilIs o'.A o'.PP.L n (P ≫ ψ) (Q ≫ ψ) (unitOn ζ) →
          Out.WeilIs o.A o.PP.L ((g.k ^ 2 * n : ℕ) : ℤ) P Q (unitOn (ζ ^ g.c))

def IsHecke {D : Datum F} {p N N' : ℕ} (g : IntSim D p) (M' : IntModel D p N') (M : IntModel D p N)
    (π : M'.X ⟶ M.X) : Prop :=
  π ≫ M.s = M'.s ∧ ∃ (o : Obj D p N M'.s) (ψ : M'.univ.A ⟶ o.A), HeckeRel g M'.univ o ψ ∧ Nonempty (ObjMap o M.univ π)

end GlobalTheory.UPel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompact
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AutGrowth

theorem height_mul_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω →
    ∃ B : ℝ, 1 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), CuspRep.height (y * c) ≤ B * CuspRep.height y := by
  intro E _ _ _ a Ω hK
  have c1 : Continuous fun u : GL (Fin a) (Cinf E) => toL u.val :=
    (Units.continuous_val : Continuous fun u : GL (Fin a) (Cinf E) => u.val)
  have c2 : Continuous fun u : GL (Fin a) (Cinf E) => toL (u⁻¹).val :=
    (Units.continuous_coe_inv : Continuous fun u : GL (Fin a) (Cinf E) => (u⁻¹).val)
  obtain ⟨M, M0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Ω, ‖toL u.val‖ ≤ M ∧ ‖toL (u⁻¹).val‖ ≤ M := by
    obtain ⟨M1, h1⟩ := hK.exists_bound_of_continuousOn c1.continuousOn
    obtain ⟨M2, h2⟩ := hK.exists_bound_of_continuousOn c2.continuousOn
    refine ⟨max 0 (max M1 M2), le_max_left _ _, fun x hx => ⟨?_, ?_⟩⟩
    · exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  have aM : 0 ≤ (a : ℝ) * M := by positivity
  refine ⟨1 + a * M, by linarith, fun u hu y => ?_⟩
  obtain ⟨m1, m2'⟩ := hM u hu
  have e2 : ((y * u)⁻¹ : GL (Fin a) (Cinf E)).val = (u⁻¹).val * (y⁻¹).val := by
    rw [_root_.mul_inv_rev]; rfl
  have p1 := norm_toL_mul_le y.val u.val
  have p2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have q1 : (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * M * ‖toL y.val‖ := by
    calc (a : ℝ) * (‖toL y.val‖ * ‖toL u.val‖) ≤ a * (‖toL y.val‖ * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m1 n1) (Nat.cast_nonneg a)
      _ = a * M * ‖toL y.val‖ := by ring
  have q2 : (a : ℝ) * (‖toL (u⁻¹).val‖ * ‖toL (y⁻¹).val‖) ≤ a * M * ‖toL (y⁻¹).val‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left m2' (Nat.cast_nonneg a)) n2
  unfold CuspRep.height
  rw [show toL (y * u).val = toL (y.val * u.val) from rfl, e2]
  nlinarith

end GlobalTheory.AutGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDerivativeOnSchwartzTensorConjStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_derivative_on_schwartz_tensor_conj : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a₁ b₁ a₂ b₂ : κ → AF F)
    (f g₁ g₂ : SInf F κ) (f₀ h : SInf F (κ ⊕ κ)),
    (∀ y, g₁ y = fderiv ℝ f y (fun i => evI F (a₁ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₁ i)) : ℝ) * f y) →
    (∀ y, g₂ y = fderiv ℝ f y (fun i => evI F (a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * evI F (b₂ i)) : ℝ) * f y) →
    (∀ x, h x = fderiv ℝ f₀ x (fun i => evI F (Sum.elim a₁ a₂ i)) - 2 * Real.pi * Complex.I *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F (Sum.elim b₁ (-b₂) i)) : ℝ) * f₀ x) →
    (∀ x, f₀ x = f (x ∘ Sum.inl) * star (f (x ∘ Sum.inr))) → ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
    h x = g₁ (x ∘ Sum.inl) * star (f (x ∘ Sum.inr)) + f (x ∘ Sum.inl) * star (g₂ (x ∘ Sum.inr)) := by
  first | exact @GlobalTheory.heisenbergDeriv_tensor_conj | exact GlobalTheory.heisenbergDeriv_tensor_conj | (intros; apply GlobalTheory.heisenbergDeriv_tensor_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperplaneSectionVanishingShiftStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperplane_section_vanishing_shift : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (F : Y.Modules) [IsFiniteQC F] (t : L.Sec) [Mono (GlobalTheory.cutHom F hL t)] (j₀ : ℤ), VanishFrom L F j₀ → VanishFrom L (GlobalTheory.cut F hL t) (j₀ + 1) ∧ ∀ j : ℤ, j₀ + 1 ≤ j → GlobalTheory.hdim k (GlobalTheory.twistZ F L j) 0 = GlobalTheory.hdim k (GlobalTheory.twistZ F L (j - 1)) 0 + GlobalTheory.hdim k (GlobalTheory.twistZ (GlobalTheory.cut F hL t) L j) 0 := by
  first | exact @GlobalTheory.HSCore.vanishFrom_cut_and_hdim | exact GlobalTheory.HSCore.vanishFrom_cut_and_hdim | (intros; apply GlobalTheory.HSCore.vanishFrom_cut_and_hdim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseNormalizationStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_inverse_normalization : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ) (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k), Y * Q' = 1 → ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k), (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  first | exact @GlobalTheory.frame_normalise_integral | exact GlobalTheory.frame_normalise_integral | (intros; apply GlobalTheory.frame_normalise_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRightStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), Y.L.IsFullLattice E → ∀ N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hY N
  first
  | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right F E n d X Y hY N
  | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right F E n d X Y hY.toIsLattice N
end

