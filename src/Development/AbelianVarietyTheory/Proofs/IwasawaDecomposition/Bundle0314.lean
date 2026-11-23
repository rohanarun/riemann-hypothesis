module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Nontrivial
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueK (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLaws.locG hL D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLaws.locG hL D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLaws.locG hL D.nd.plOm η' w).unr ∧ (ParLaws.locG hL D.nd.plOm η' w).frobEig = (ParLaws.locG hL D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ, (ParLaws.locG hL D.nd.plOm η w).frobEig = {a} →
      (ParLaws.locG hL D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLaws.laws hL hF D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) ↔ (ParLaws.locG hL D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLaws.locG hL D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = (ParLaws.locG hL D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {_π : HostCGu D.host a // 0 < a}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLaws.locG hL D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w)
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos⟩
    etaTinv := ⟨η', one_pos⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueCG (hL hF) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (η η' h1 h2 h3 h4) :
    CGTrue hL (setCG D hE (trueK hL hF D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  surj := fun _ h π => ⟨⟨π, h⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtSqIntegralFormEqClassSumMetric
section
noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
open scoped Matrix ComplexOrder

attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem map_conj_bVV {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (i : VVIdx lam) :
    MvPolynomial.map ((starRingEnd ℂ).comp φ) (bVV K lam i : VV K lam).1 = MvPolynomial.map φ (bVV K lam i : VV K lam).1 := by
  obtain ⟨Q, hQ⟩ := bVVfun_int K lam i
  rw [bVV_coe, hQ, MvPolynomial.map_map, MvPolynomial.map_map]
  rw [RingHom.ext_int (((starRingEnd ℂ).comp φ).comp (Int.castRingHom K)) (φ.comp (Int.castRingHom K))]

theorem map_smul_pol {K : Type} [Field K] {σ : Type} (φ : K →+* ℂ) (r : K) (p : MvPolynomial σ K) :
    MvPolynomial.map φ (r • p) = φ r • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem pairB_conj_map {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (φ : K →+* ℂ)
    (y : VV K lam) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map φ y.1)) (MvPolynomial.map φ y.1) =
      star (fun i => φ ((bVV K lam).repr y i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map φ *ᵥ (fun i => φ ((bVV K lam).repr y i)) := by
  have hy : y.1 = ∑ i, (bVV K lam).repr y i • (bVV K lam i : VV K lam).1 := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    rw [Submodule.coe_sum]
    rfl
  rw [MvPolynomial.map_map, hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul_pol, map_conj_bVV, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← GlobalTheory.PeriodOnStep.map_pairB, dotProduct, Matrix.mulVec, Matrix.map_apply, GlobalTheory.TestLat.Compare.gramB, Matrix.of_apply, pairBK_apply,
    Pi.star_apply, RingHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem herm_mk {K : Type} [Field K] {ι : Type} [Fintype ι] (M : Matrix ι ι K) (φ : K →+* ℂ) (hM : (M.map φ).PosDef)
    (a : ι → K) :
    star (fun i => (InfinitePlace.mk φ).embedding (a i)) ⬝ᵥ M.map (InfinitePlace.mk φ).embedding *ᵥ
        (fun i => (InfinitePlace.mk φ).embedding (a i)) =
      star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h]
    have hr := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => φ (a i))
    have hc : starRingEnd ℂ (star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i))) =
        star (fun i => φ (a i)) ⬝ᵥ M.map φ *ᵥ (fun i => φ (a i)) :=
      Complex.conj_eq_iff_im.2 (Complex.nonneg_iff.1 hr).2.symm
    rw [← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
      map_mul, starRingEnd_apply, star_star]

theorem normAt_sq_eq_cSum {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V) :
    ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) =
      cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  have h0 := (GlobalTheory.PeriodOnStep.isFormsOf_MtildeH B.wts I.Ch I.sel (I.tup a) I.Ps hX).2 (InfinitePlace.mk B.embLL)
  refine (h0 (x : (MtildeH B.wts I.Ch hX I.sel (I.tup a) I.Ps).V)).trans ?_
  rw [cSum_apply]
  unfold GSD.ipAt
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold cTerm
  rw [GSD.wt_eq]
  congr 1
  rw [GlobalTheory.PeriodClassSum.pairAt_eq, GlobalTheory.PeriodClassSum.row_gramV]
  exact (herm_mk _ _ (GlobalTheory.PeriodClassSum.gramB_posDef _ _) _).trans (pairB_conj_map _ _ _).symm

end GlobalTheory.Mem.Df
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PairingComplexFormsConstOnRowClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df

attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

variable {X : Fields} {n : ℕ}
open Matrix

theorem ufGL_apply_single (γ : UF X.E n) (i j : Fin n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) i j = (γ.1 (Pi.single j 1)) i := by
  simp [ufGL, toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem ufGL_unitary (γ : UF X.E n) :
    ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E)ᴴ * (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E) = 1 := by
  ext j k
  have h := γ.2 (Pi.single j 1) (Pi.single k 1)
  simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, ufGL_apply_single]
  rw [h]
  simp only [Pi.single_apply, Matrix.one_apply]
  simp [eq_comm]
  split_ifs <;> simp

theorem bc_conj_unitary (hX : X.Ok) (φ : X.E →+* ℂ) (γ : UF X.E n) :
    Formalism.UG.bc (starRingEnd ℂ) (Formalism.UG.bc φ (ufGL X.E n γ)) = inside₂ ℂ n (Formalism.UG.bc φ (ufGL X.E n γ)) := by
  set A := Formalism.UG.bc φ (ufGL X.E n γ)
  have hA : (A : Matrix (Fin n) (Fin n) ℂ) = (ufGL X.E n γ : Matrix (Fin n) (Fin n) X.E).map φ := rfl
  have h1 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * (A : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have := congrArg (fun M => M.map φ) (ufGL_unitary γ)
    simp only [Matrix.map_mul, Matrix.map_one _ φ.map_zero φ.map_one] at this
    rw [← this, hA]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply, hX.conjE]
  apply Units.ext
  show (A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ) = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ
  have h2 : ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    calc _ = ((A : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * ((A : Matrix (Fin n) (Fin n) ℂ) * ((A⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← h2, Matrix.transpose_transpose]

theorem map_conj_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p : Pol ℂ X.Tau n) :
    MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p) =
      actP lam (invTrK (embGL (embAt σ X.emb) (ufGL X.E n γ))) (MvPolynomial.map (starRingEnd ℂ) p) := by
  rw [rhoC_apply]
  refine (GlobalTheory.ValCmp.use₂ (starRingEnd ℂ) lam _ p).trans ?_
  congr 2
  funext τ
  exact bc_conj_unitary hX (embAt σ X.emb τ) γ

theorem pairB_rhoC (hX : X.Ok) (σ : X.K →+* ℂ) (lam : X.Tau → DomWeight n) (γ : UF X.E n) (p q : Pol ℂ X.Tau n) :
    pairB lam (MvPolynomial.map (starRingEnd ℂ) (rhoC σ lam γ p)) (rhoC σ lam γ q) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) p) q := by
  rw [map_conj_rhoC hX σ lam γ p, rhoC_apply]
  exact pairingBInvariantK_holds ℂ X.Tau n lam _ _ q

theorem conj_mul_self_chr {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (h : ↥Λ.grp) :
    starRingEnd ℂ (σ (Λ.chr h : X.Kˣ)) * σ (Λ.chr h : X.Kˣ) = 1 := by
  obtain ⟨N, hN, hp⟩ := (isOfFinOrder_of_finite h).exists_pow_eq_one
  have h1 : (σ (Λ.chr h : X.Kˣ)) ^ N = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hp, map_one, Units.val_one, map_one]
  have h2 := Complex.norm_eq_one_of_pow_eq_one h1 hN.ne'
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]
  simp

theorem pairB_conj_cls_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a)
    (d d' : (rowS I a).D), (rowS I a).cls d = (rowS I a).cls d' →
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d)) (G.1 d) =
      pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 d')) (G.1 d') := by
  intro B X I hX a F G d d' h
  obtain ⟨g, rfl⟩ := ((rowS I a).cls_eq_iff _ _).1 h
  have hF := (F.2 d').2 g
  have hG := (G.2 d').2 g
  letI := (rowS I a).actD
  erw [hF, hG]
  rw [map_conj_smul, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [pairB_rhoC hX, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (B.embLL _)]
  have hc := conj_mul_self_chr B.embLL (rowTy I.Ch I.sel (I.tup a) I.Ps).inv g.2
  rw [hc, one_mul]

end GlobalTheory.Mem.Df
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReGLMemLevelVL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TwistLevel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reGL_rfl_apply {a : ℕ} {R : Type} [CommRing R] (x : GL (Fin a) R) : reGL (rfl : a = a) R x = x := by
  ext i j
  rfl

theorem reL_rfl' {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_mem_UPts (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (R : Type) [CommRing R] [Algebra F R] (x : GL (Fin a) (E ⊗[F] R)) :
    reGL h _ x ∈ UPts σ J R ↔ x ∈ UPts σ G R := by
  subst h
  subst hJ
  rw [reGL_rfl_apply]
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem reGL_mem_levelVL (σ : E →ₐ[F] E) {a b : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E) (J : Matrix (Fin b) (Fin b) E)
    (hJ : J = G.reindex (finCongr h) (finCongr h)) (v : HeightOneSpectrum (𝓞 F)) (L : Submodule (𝓞 E) (Fin a → E))
    (x : GL (Fin a) (E ⊗[F] v.adicCompletion F)) :
    reGL h _ x ∈ levelVL σ J v (reL h L) ↔ x ∈ levelVL σ G v L := by
  subst h
  subst hJ
  rw [reGL_rfl_apply, reL_rfl']
  simp only [finCongr_refl, Matrix.reindex_refl_refl]

theorem exists_off (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hκ : κ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ Q, bc (prV (E := E) v) y = 1) ∧
      ∀ v, v ∉ Q → bc (prV (E := E) v) y = bc (prV (E := E) v) κ := by
  classical

  have key : ∀ (y : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v w : HeightOneSpectrum (𝓞 F)), w ≠ v →
      bc (prV (E := E) w) (Formalism.UG.P.afsplitU v 1 y) = bc (prV (E := E) w) y := by
    intro y v w hw
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe,
      Formalism.UG.P.afsplitC_prV_ne v w hw]
  induction Q using Finset.induction_on with
  | empty => exact ⟨κ, hκ, by simp, fun v _ => rfl⟩
  | @insert v Q hv ih =>
    obtain ⟨y, hy, h1, h2⟩ := ih
    refine ⟨Formalism.UG.P.afsplitU v 1 y, Formalism.UG.P.afsplitU_mem v σ J _ _ (one_mem _) hy, ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst hwv
        exact Formalism.UG.P.afsplit_right1 w 1 y
      · rw [key y v w hwv]
        exact h1 w ((Finset.mem_insert.mp hw).resolve_left hwv)
    · intro w hw
      have hwv : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self v Q)
      rw [key y v w hwv]
      exact h2 w (fun h => hw (Finset.mem_insert_of_mem h))

end Gen

section Lev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {hc : CMData F E} {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ}


open Classical in
def ulocQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)) :=
  if h : v ∈ Q then W v h else H0.Uloc v

theorem ulocQ_pos (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ Q) :
    ulocQ H0 Q W v = W v h := by
  unfold ulocQ
  exact dif_pos h

theorem ulocQ_neg (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ Q) :
    ulocQ H0 Q W v = H0.Uloc v := by
  unfold ulocQ
  exact dif_neg h

def uQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))) :
    Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)) where
  carrier := {x | x ∈ Formalism.L2.Herm.UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ ulocQ H0 Q W v}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, fun v => by rw [map_mul]; exact mul_mem (hx.2 v) (hy.2 v)⟩
  one_mem' := ⟨one_mem _, fun v => by rw [map_one]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, fun v => by rw [map_inv]; exact inv_mem (hx.2 v)⟩

def mkLevQ (H0 : Formalism.L2.Herm.StepLevel hc S gp T f) (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (W : ∀ v, v ∈ Q → Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hWl : ∀ v hv, W v hv ≤ levelVL hc.sig S.gram v H0.Lb)
    (hWQ : ∀ v hv, ∃ N : ℕ, 0 < N ∧ ∀ x, Formalism.L2.Herm.InPrinc hc S v N H0.Lb x → x ∈ W v hv)
    (hQg : ∀ v ∈ Q, ∀ i, (gp i : 𝓞 F) ∉ v.asIdeal) (hQT : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal) :
    Formalism.L2.Herm.StepLevelQ hc S gp T f Q where
  Lb := H0.Lb
  Lb_fin := H0.Lb_fin
  Lb_span := H0.Lb_span
  Lb_int := H0.Lb_int
  Lb_dual := H0.Lb_dual
  Lb_index := H0.Lb_index
  Uloc := ulocQ H0 Q W
  Uloc_lev v := by
    by_cases h : v ∈ Q
    · rw [ulocQ_pos H0 Q W h]; exact hWl v h
    · rw [ulocQ_neg H0 Q W h]; exact H0.Uloc_lev v
  Uloc_hyp v h0 h1 hT hQ := by rw [ulocQ_neg H0 Q W hQ]; exact H0.Uloc_hyp v h0 h1 hT
  Uloc_g i v h x hx := by
    rw [ulocQ_neg H0 Q W (fun hq => hQg v hq i h)]; exact H0.Uloc_g i v h x hx
  UlocAlt v h x := by
    rw [ulocQ_neg H0 Q W (fun hq => hQT v hq h)]; exact H0.UlocAlt v h x
  Uloc_Q v hv := by
    obtain ⟨N, hN, h⟩ := hWQ v hv
    exact ⟨N, hN, fun x hx => by rw [ulocQ_pos H0 Q W hv]; exact h x hx⟩
  U := uQ H0 Q W
  U_eq _ := Iff.rfl

end Lev

end GlobalTheory.Mem.Col2.TwistLevel

end

namespace GlobalTheory.Mem.Col2.TwistLevel

section Abs

def actOfRed {G : Type} [Group G] {ι : Type} {n : ℕ} {k : ι → Type} [∀ i, CommRing (k i)]
    (ρ : G → ∀ i, Matrix (Fin n) (Fin n) (k i)) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b) :
    MulAction G (∀ i, Fin n → k i) where
  smul a y i := ρ a i *ᵥ y i
  one_smul y := by
    funext i
    show ρ 1 i *ᵥ y i = y i
    rw [h1, Pi.one_apply, Matrix.one_mulVec]
  mul_smul a b y := by
    funext i
    show ρ (a * b) i *ᵥ y i = ρ a i *ᵥ (ρ b i *ᵥ y i)
    rw [hm, Pi.mul_apply, Matrix.mulVec_mulVec]

theorem assemble {G : Type} [Group G] {Ch : Type} [Finite Ch] {Qt : Type} [Finite Qt] (Wq : Qt → Type) [∀ q, Group (Wq q)]
    (zQ : G →* ∀ q, Wq q) (Kc : Ch → ∀ q, Subgroup (Wq q)) (hfi : ∀ β q, (Kc β q).FiniteIndex) {V : Type} [Finite V]
    [MulAction G V] (w : Ch → V) (H : Ch → Subgroup G)
    (hH : ∀ β κ, κ ∈ H β ↔ (∀ q, zQ κ q ∈ Kc β q) ∧ κ • w β = w β) :
    ∃ (Yb : Type) (_ : Finite Yb) (_ : MulAction G Yb) (yb : Ch → Yb) (yG : Yb → V) (YQ : Type) (yQ : Yb → YQ),
      (∀ y, ∃! β, ∃ κ : G, κ • yb β = y) ∧ (∀ β (κ : G), κ ∈ H β ↔ κ • yb β = yb β) ∧ (∀ (κ : G) y, yG (κ • y) = κ • yG y) ∧
      (∀ y y', yG y = yG y' → yQ y = yQ y' → y = y') ∧ (∀ (κ : G) y, zQ κ = 1 → yQ (κ • y) = yQ y) := by
  classical
  have hfq : ∀ β q, Finite (Wq q ⧸ Kc β q) := fun β q => by
    haveI := hfi β q
    infer_instance

  let fQ : ∀ β, G ⧸ H β → ∀ q, Wq q ⧸ Kc β q := fun β c =>
    Quotient.liftOn' c (fun g q => ((zQ g q : Wq q) : Wq q ⧸ Kc β q)) (by
      intro a b hab
      have hm := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).1
      funext q
      apply QuotientGroup.eq.mpr
      simpa [map_mul, map_inv] using hm q)

  let fG : ∀ β, G ⧸ H β → V := fun β c =>
    Quotient.liftOn' c (fun g => g • w β) (by
      intro a b hab
      have hs := ((hH β (a⁻¹ * b)).mp (QuotientGroup.leftRel_apply.mp hab)).2
      rw [mul_smul, inv_smul_eq_iff] at hs
      exact hs.symm)
  have hinj : ∀ (y y' : Σ β, G ⧸ H β), fG y.1 y.2 = fG y'.1 y'.2 →
      (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨y'.1, fQ y'.1 y'.2⟩ → y = y' := by
    rintro ⟨β, c⟩ ⟨β', c'⟩ hG hQ
    obtain rfl : β = β' := congrArg Sigma.fst hQ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective c'
    have hQ' : fQ β g = fQ β g' := eq_of_heq (Sigma.mk.inj hQ).2
    have hG' : g • w β = g' • w β := hG
    have hmem : g⁻¹ * g' ∈ H β := by
      refine (hH β _).mpr ⟨fun q => ?_, ?_⟩
      · have hq : ((zQ g q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g' q : Wq q) : Wq q ⧸ Kc β q) := congrFun hQ' q
        have := QuotientGroup.eq.mp hq
        simpa [map_mul, map_inv] using this
      · rw [mul_smul, ← hG', inv_smul_smul]
    exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr hmem)
  refine ⟨Σ β, G ⧸ H β,
    Finite.of_injective (fun y => (fG y.1 y.2, (⟨y.1, fQ y.1 y.2⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q)))
      (fun y y' h => hinj y y' (congrArg Prod.fst h) (congrArg Prod.snd h)),
    inferInstance, fun β => ⟨β, ((1 : G) : G ⧸ H β)⟩, fun y => fG y.1 y.2,
    Σ β, ∀ q, Wq q ⧸ Kc β q, fun y => ⟨y.1, fQ y.1 y.2⟩, ?_, ?_, ?_, hinj, ?_⟩
  · rintro ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨β, ⟨g, ?_⟩, ?_⟩
    · show (⟨β, g • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (g : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    · rintro β' ⟨κ, hκ⟩
      exact congrArg Sigma.fst hκ
  · intro β κ
    have e : κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩ := by
      show (⟨β, κ • ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, (κ : G ⧸ H β)⟩
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    show κ ∈ H β ↔ κ • (⟨β, ((1 : G) : G ⧸ H β)⟩ : Σ β, G ⧸ H β) = ⟨β, ((1 : G) : G ⧸ H β)⟩
    rw [e]
    constructor
    · intro hk
      exact congrArg (Sigma.mk β) (QuotientGroup.eq.mpr (by simpa using hk))
    · intro hk
      have h2 : (κ : G ⧸ H β) = ((1 : G) : G ⧸ H β) := eq_of_heq (Sigma.mk.inj hk).2
      simpa using QuotientGroup.eq.mp h2
  · rintro κ ⟨β, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show fG β (κ • (g : G ⧸ H β)) = κ • fG β g
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    exact mul_smul κ g (w β)
  · rintro κ ⟨β, c⟩ hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    show (⟨β, fQ β (κ • (g : G ⧸ H β))⟩ : Σ β, ∀ q, Wq q ⧸ Kc β q) = ⟨β, fQ β g⟩
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    refine congrArg (Sigma.mk β) (funext fun q => ?_)
    show ((zQ (κ * g) q : Wq q) : Wq q ⧸ Kc β q) = ((zQ g q : Wq q) : Wq q ⧸ Kc β q)
    rw [map_mul, hk, one_mul]

end Abs

end GlobalTheory.Mem.Col2.TwistLevel
end

