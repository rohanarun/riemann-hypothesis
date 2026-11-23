module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1511
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenBasisSameVec
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates

theorem exists_eigEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] {a : OAct O G} {a' : OAct O G'}
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R : Type} [CommRing R] (x : Sp R ⟶ S')
    (x' : Sp R ⟶ S) (hx : x' = x ≫ f) :
    ∃ e : (epsAt x ⟶ G') ≃ (epsAt x' ⟶ G), (∀ v, (e v).left = v.left ≫ φ) ∧
      ∀ (χ : O →+* R) (n : ℕ) (v : Fin n → (epsAt x ⟶ G')),
        IsEigenBasis a' x χ v ↔ IsEigenBasis a x' χ (fun i => e (v i)) := by
  subst hx
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsAt x ⟶ G'), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  refine ⟨e.toEquiv, he, fun χ n v => ?_⟩
  have hP : ∀ v : epsAt x ⟶ G', IsEigenTangent a' x χ v ↔ IsEigenTangent a (x ≫ f) χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin n → (epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin n → R) (w : epsAt x ⟶ G'), IsCombination x c (fun i => (v i).left) w ↔
      IsCombination (x ≫ f) c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_eigenBasis_sameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n) :
    ∃ v : Fin n → (epsAt ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _) ⟶ Y.t.G),
      IsEigenBasis Y.t.act _ (chr c τ (algebraMap c.F S)) v ∧
      ∀ i : Fin n, ∃ j : Fin (Dw.mult τ), (j : ℕ) = i ∧ SameVec Y y (y.u τ j) (v i).left := by
  subst hn
  obtain ⟨e₀, he₀, hb₀⟩ := exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act (ptF y) y.x
    (pullback.lift_fst _ _ _).symm
  obtain ⟨e, he, hb⟩ := exists_eigEquiv Y.m.cart Y.m.act (ptF y) ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _)
    (Category.assoc _ _ _)
  let u : Fin (Dw.mult τ) → (epsAt y.x ⟶ Xo.univ.t.G) := fun i => Over.homMk (y.u τ i) (y.tan τ i).1
  have hu : IsEigenBasis Xo.univ.t.act y.x (chr c τ (algebraMap c.F S)) u := by
    refine ⟨fun i => ⟨(y.tan τ i).2, fun a => y.eig τ i a⟩, fun w hw => ?_⟩
    refine (existsUnique_congr fun a => ⟨?_, ?_⟩).1 (y.basis τ w.left ⟨Over.w w, hw.1⟩ fun a => hw.2 a)
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, Over.OverMorphism.ext h2.symm⟩
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, congrArg (fun z => z.left) h2.symm⟩
  have hw := (hb₀ (chr c τ (algebraMap c.F S)) _ fun i => e₀.symm (u i)).2
    ((funext fun i => e₀.apply_symm_apply (u i) : (fun i => e₀ (e₀.symm (u i))) = u).symm ▸ hu)
  refine ⟨fun i => e (e₀.symm (u i)), (hb _ _ _).1 hw, fun i => ⟨i, rfl, (e₀.symm (u i)).left,
    ⟨Over.w _, (hw.1 i).1⟩, ?_, (he _).symm⟩⟩
  rw [← he₀, Equiv.apply_symm_apply]
  rfl

theorem exists_matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) (hy : ∀ s, ptF y s ∈ (V : Set (Xo.XF c))) :
    ∃ a : Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a := by
  obtain ⟨v, hv, ev⟩ := exists_eigenBasis_sameVec Y y τ.1 Dw.p (if_pos τ.2)
  obtain ⟨w, hw, ew⟩ := exists_eigenBasis_sameVec Y y (conjEmb τ.1) Dw.q (if_neg (conj_not_mem τ))
  refine ⟨⟨ptF y ≫ Y.jQ, by rw [Category.assoc, Y.jQ_over, ptF, pullback.lift_snd], ?_, v, w, hv, hw⟩,
    rfl, ev, ew⟩
  rintro _ ⟨z, rfl⟩
  exact subset_closure ⟨ptF y z, hy z, by simp⟩

end GlobalTheory.BdryUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalMatrixApproxTwoAdelicModuli
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.BotPairSmall.CongApprox

theorem approx_two_moduli : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)), 𝔫 ≠ ⊥ → ∀ (a d : ℕ) (M : Matrix (Fin d) (Fin a) (AE D)) (m : ℕ), 0 < m → ∃ z : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, ∃ y ∈ IhE D ⊤, (z.map (inc D) - M) i l = (m : AE D) * y) ∧ ∀ i l, (M - z.map (inc D)) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 h𝔫 a d M m hm
  obtain ⟨n, hn, hnI⟩ := GlobalTheory.CompletedLattice.exists_mul_IhE_mem D ⊤
  have hN : 0 < Ideal.absNorm 𝔫 := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨z, hz⟩ := GlobalTheory.NormSum.VacMove.MI_approx (D := D) (cc := ⊤) top_ne_bot M (m * (n * Ideal.absNorm 𝔫))
    (Nat.mul_pos hm (Nat.mul_pos hn hN))
  refine ⟨z, GlobalTheory.NormSum.VacMove.MI.of_dvd (dvd_mul_right m _) hz, fun i l => ?_⟩
  obtain ⟨y, hy, e⟩ := hz i l
  have hny : (n : AE D) * y ∈ OhE D := hnI y hy
  have hmny : (m : AE D) * ((n : AE D) * y) ∈ OhE D := mul_mem (natCast_mem _ m) hny
  have h2 := GlobalTheory.BotPairSmall.BlockIdx.absNorm_mul_mem_hatId D 𝔫 hmny
  have e2 : (M - z.map (inc D)) i l = -((Ideal.absNorm 𝔫 : AE D) * ((m : AE D) * ((n : AE D) * y))) := by
    rw [← neg_sub, Matrix.neg_apply, e]; push_cast; ring
  rw [e2]
  exact neg_mem h2

end GlobalTheory.BotPairSmall.CongApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHyperbolicPlaneSplitHermitianLatticeSpace
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KTowerPlane

section Help
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (a b : Fin n → E) : form σ J b a = σ (form σ J a b) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => hJ j i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by simp [form, add_dotProduct]

theorem form_sub_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a - b) c = form σ J a c - form σ J b c := by simp [form, sub_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J (s • a) c = s * form σ J a c := by simp [form, smul_dotProduct]

theorem form_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a + b) = form σ J c a + form σ J c b := by
  have : (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J c (s • a) = σ s * form σ J c a := by
  have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_gram {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (u u' : Fin n₁ → E) :
    form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  have e1 : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) ι u' i
  simp only [form, e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem map_form (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    e (form σ J a b) = (fun i => e (a i)) ⬝ᵥ J.map e *ᵥ star (fun i => e (b i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, h.2.2.2 e]

theorem transpose_mulVec_eq_zero {n n₁ : ℕ} {R : Type} [CommRing R] (ι : Matrix (Fin n) (Fin n₁) R) (w : Fin n → R)
    (hw : ∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) : ιᵀ *ᵥ w = 0 := by
  funext k
  have := hw (Pi.single k 1)
  rwa [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this

theorem map_herm (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) : (J.map e)ᴴ = J.map e := by
  ext i j
  simp [Matrix.conjTranspose_apply, ← h.2.2.2 e, hJ]

theorem map_orth (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E) (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) :
    (ι.map e)ᵀ *ᵥ (J.map e *ᵥ star (fun i => e (x i))) = 0 := by
  have h0 : ιᵀ *ᵥ (J *ᵥ fun i => σ (x i)) = 0 := transpose_mulVec_eq_zero ι _ hx
  have hs : star (fun i => e (x i)) = fun i => e (σ (x i)) := funext fun i => by simp [h.2.2.2 e]
  have e2 : (J.map e *ᵥ fun i => e (σ (x i))) = fun i => e ((J *ᵥ fun i => σ (x i)) i) :=
    funext fun i => (RingHom.map_mulVec e J _ i).symm
  have e3 : (ιᵀ.map e *ᵥ fun i => e ((J *ᵥ fun i => σ (x i)) i)) = fun k => e ((ιᵀ *ᵥ (J *ᵥ fun i => σ (x i))) k) :=
    funext fun k => (RingHom.map_mulVec e ιᵀ _ k).symm
  rw [hs, ← Matrix.transpose_map, e2, e3, h0]
  funext k
  simp

theorem map_gram (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) : (ι.map e)ᵀ * J.map e * (ι.map e).map star = (ιᵀ * J * ι.map σ).map e := by
  have : (ι.map e).map star = (ι.map σ).map e := by ext i j; simp [h.2.2.2 e]
  rw [this, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

end Help

section Help2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem form_single {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j <;> simp [h]
  simp [form, this, Matrix.mulVec_single, single_dotProduct]
end Help2

theorem exists_hyperbolic_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  classical
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨x₀, hx₀, hx₀x₀⟩ := _root_.GlobalTheory.HermIso.exists_isotropic F E σ B hB n Y r s (by omega) hr hs hY
  obtain ⟨x, y, hxx, hyy, hxy, hL, hP⟩ := _root_.GlobalTheory.HypPairLat.exists_pair F E σ B hB n Y r s hY x₀ hx₀ hx₀x₀
  obtain ⟨ι, P, hPι, horth, hcomp⟩ := _root_.GlobalTheory.exists_orthCompl_hypPair F E σ n n₁ Y.J x y hn hY.herm hxx hyy hxy
  have hyx : form σ Y.J y x = 1 := by rw [form_swap hcm hY.herm, hxy, map_one]
  have hsplit : ∀ z ∈ Y.L, ∃ u, ι *ᵥ u ∈ Y.L ∧ z = form σ Y.J z y • x + ι *ᵥ u + form σ Y.J z x • y := by
    intro z hz
    obtain ⟨u, hu⟩ := hcomp (z - form σ Y.J z y • x - form σ Y.J z x • y) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxx, hyx]; ring) (by
        rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, hxy, hyy]; ring)
    refine ⟨u, ?_, ?_⟩
    · rw [← hu]; exact Y.L.sub_mem (Y.L.sub_mem hz (hL z hz).1) (hL z hz).2
    · rw [← hu]; abel
  set L₁ := Y.L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E)) with hL₁def
  have hlat₁ : L₁.IsFullLattice E := by
    refine { toIsLattice := GlobalTheory.T.isLattice_comap_mulVecLin_of_leftInverse_matrix E n n₁ Y.L ι P hPι hY.lat.toIsLattice, span_eq_top := ?_ }
    refine eq_top_iff.2 fun u _ => ?_
    have hu : ι *ᵥ u ∈ Submodule.span E (Y.L : Set (Fin n → E)) :=
      hY.lat.span_eq_top ▸ Submodule.mem_top
    obtain ⟨z, hz, d, hd⟩ := (IsLocalization.mem_span_iff (M := nonZeroDivisors (𝓞 E))).1 hu
    have hdu : (d : 𝓞 E) • u ∈ L₁ := by
      change ι *ᵥ ((d : 𝓞 E) • u) ∈ Y.L
      rw [Matrix.mulVec_smul, hd, ← IsScalarTower.algebraMap_smul E (d : 𝓞 E), smul_smul,
        IsLocalization.mk'_spec', map_one, one_smul]
      simpa only [Submodule.span_eq] using hz
    have h := (Submodule.span E (L₁ : Set (Fin n₁ → E))).smul_mem
      (IsLocalization.mk' E 1 d) (Submodule.subset_span hdu)
    rwa [← IsScalarTower.algebraMap_smul E (d : 𝓞 E), smul_smul,
      IsLocalization.mk'_spec, map_one, one_smul] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp [form] at hxy
  obtain ⟨𝔟, h𝔟⟩ := _root_.GlobalTheory.latticeLine_fractionalIdeal E n Y.L hY.lat.toIsLattice x hx0
  set J₁ := ιᵀ * Y.J * ι.map σ with hJ₁
  have hform₁ : ∀ u u', form σ J₁ u u' = form σ Y.J (ι *ᵥ u) (ι *ᵥ u') := form_gram Y.J ι
  let e : InfinitePlace F → E →+* ℂ := fun w => (B.emb w).1
  have hMh : ∀ w, (Y.J.map (e w))ᴴ = Y.J.map (e w) := fun w => map_herm hcm _ hY.herm
  have cxx : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (x i)) = 0 := fun w => by
    rw [← map_form hcm, hxx, map_zero]
  have cyy : ∀ w, (fun i => e w (y i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 0 := fun w => by
    rw [← map_form hcm, hyy, map_zero]
  have cxy : ∀ w, (fun i => e w (x i)) ⬝ᵥ Y.J.map (e w) *ᵥ star (fun i => e w (y i)) = 1 := fun w => by
    rw [← map_form hcm, hxy, map_one]
  have cox : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (x i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι x (fun u => (horth u).1)
  have coy : ∀ w, (ι.map (e w))ᵀ *ᵥ (Y.J.map (e w) *ᵥ star (fun i => e w (y i))) = 0 := fun w =>
    map_orth hcm _ Y.J ι y (fun u => (horth u).2)
  have cP : ∀ w, P.map (e w) * ι.map (e w) = 1 := fun w => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have cg : ∀ w, (ι.map (e w))ᵀ * Y.J.map (e w) * (ι.map (e w)).map star = J₁.map (e w) := fun w =>
    map_gram hcm _ Y.J ι
  have hsig₁ : ∀ w, HasSig (J₁.map (e w)) (r - 1) (s - 1) := fun w => by
    rw [← cg w]
    exact _root_.GlobalTheory.PlaneSig.hasSig_complement_plane n n₁ _ _ _ _ _ r s hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (hY.sig w)
  have hθ₁ : ∀ w, ∃ θ, IsCartan (J₁.map (e w)) θ := fun w => _root_.GlobalTheory.CartanEx.exists_isCartan n₁ _ _ _ (hsig₁ w)
  choose θ₁ hθ₁ using hθ₁
  have hθ : ∀ w, ∃ θ, IsCartan (Y.J.map (e w)) θ ∧ θ * ι.map (e w) = ι.map (e w) * θ₁ w ∧
      θ *ᵥ (fun i => e w (x i)) = fun i => e w (y i) := fun w =>
    _root_.GlobalTheory.CartanPlane.extend_swap n n₁ _ _ _ _ _ _ hn (hMh w) (cxx w) (cyy w) (cxy w) (cox w) (coy w) (cP w) (by rw [cg w]; exact hθ₁ w)
  choose θ hθ using hθ
  haveI := hlat₁
  have hb₁ : ∀ v : B.P, ∃ β, IsSplitBasis (B.τ v) L₁ β := fun v => exists_isSplitBasis (B.τ v) L₁ hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : Pl (F := F), GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map (B.τ v) * (β₁ v).1) r j) ∧
      IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.PlaneBasis.exists_isSplitBasis_plane F E σ hcm v (B.τ v) n n₁ Y.L x y ι (β₁ v) i₀ i₁ hn h01 h1n hY.lat
      (fun z hz => by
        obtain ⟨u, hu, hz'⟩ := hsplit z hz
        exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩) (hP v).1 (hP v).2 (hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : Pl (F := F), GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y₁ : Spc F E n₁ := ⟨J₁, L₁, θ₁, bas₁⟩
  let Y' : Spc F E n := ⟨Y.J, Y.L, θ, bas⟩
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact { herm := hY.herm, sig := hY.sig, lat := hY.lat, dual := hY.dual, cartan := fun w => (hθ w).1
            bas := fun v => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v]
              exact (hβ v).2 }
  · exact { herm := fun i j => by
              show σ (J₁ j i) = J₁ i j
              rw [← form_single (σ := σ) J₁ j i, ← form_single (σ := σ) J₁ i j, hform₁, hform₁,
                form_swap hcm hY.herm (ι *ᵥ Pi.single j 1) (ι *ᵥ Pi.single i 1)]
            sig := hsig₁
            lat := hlat₁
            dual := fun u => by
              show u ∈ L₁ ↔ ∀ u' ∈ L₁, IsIntegral ℤ (form σ J₁ u u')
              refine ⟨fun hu u' hu' => ?_, fun H => ?_⟩
              · rw [hform₁]; exact (hY.dual _).1 hu _ hu'
              · show ι *ᵥ u ∈ Y.L
                refine (hY.dual _).2 fun z hz => ?_
                obtain ⟨u', hu', hz'⟩ := hsplit z hz
                rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (horth u).1,
                  (horth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform₁]
                exact H u' hu'
            cartan := hθ₁
            bas := fun v => by
              rw [show Y₁.bas v = β₁ v from hbas₁ v]
              exact hβ₁ v }
  · exact { rank := hn, xx := hxx, yy := hyy, xy := hxy, orth := horth, gram := rfl, low := fun u => Iff.rfl
            split := fun z hz => by
              obtain ⟨u, hu, hz'⟩ := hsplit z hz
              exact ⟨_, _, u, (hL z hz).1, (hL z hz).2, hu, hz'⟩
            ideal := h𝔟
            cartan := fun w => ⟨(hθ w).2.1, 1, one_ne_zero, by rw [one_smul]; exact (hθ w).2.2.symm⟩
            bas := fun v i => by
              rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show Y₁.bas v = β₁ v from hbas₁ v]
              exact (hβ v).1 i }

end GlobalTheory.KTowerPlane
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongApprox

theorem inc_mem_OhE (D : D7) (x : 𝓞 D.host.E) : inc D (x : D.host.E) ∈ OhE D :=
  Formalism.UG.P.easyc_inclE_mem _ _ _ (RingHom.mem_range.2 ⟨x, rfl⟩)

theorem exists_int_approx (D : D7) (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ b : 𝓞 D.host.E, ∃ w ∈ OhE D, s = inc D (b : D.host.E) + (n : AE D) * w := by
  rw [← GlobalTheory.AdelicApprox.levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨b, t, ht, h⟩

theorem OhE_le_IhE_top (D : D7) (s : AE D) (hs : s ∈ OhE D) : s ∈ IhE D ⊤ := by
  have h := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ s hs
  simpa [Ideal.absNorm_top] using h

theorem mul_mem_hatId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (x : AE D) (hx : x ∈ OhE D)
    (t : AE D) (ht : t ∈ hatId D 𝔪) : x * t ∈ hatId D 𝔪 := by
  unfold hatId at ht ⊢
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (t : AE D)
    (ht : t ∈ hatId D 𝔪) :
    ∃ b ∈ 𝔪, ∃ y ∈ IhE D ⊤, inc D (b : D.host.E) - t = (m : AE D) * y := by
  unfold hatId at ht
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    obtain ⟨c, w, hw, hsw⟩ := exists_int_approx D m hm s hs
    refine ⟨b * c, Ideal.mul_mem_right c 𝔪 hb, -(inc D (b : D.host.E) * w),
      OhE_le_IhE_top D _ (neg_mem (mul_mem (inc_mem_OhE D b) hw)), ?_⟩
    rw [hsw]
    push_cast
    rw [map_mul]
    ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    obtain ⟨b', hb', u', hu', h'⟩ := hy'
    refine ⟨b + b', add_mem hb hb', u + u', add_mem hu hu', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination h + h'
  | neg y _ hy =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    refine ⟨-b, neg_mem hb, -u, neg_mem hu, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -h

end GlobalTheory.CongApprox

namespace GlobalTheory.CongApprox

theorem exists_closeTo_congOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (k : GA D a), k ∈ intG D a → CongOne D 𝔪 k → ∀ (z : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ CloseTo D ⊤ m (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) z (z + w) := by
  intro D 𝔪 _ a d k hk hcong z _ m hm
  have hinv : CongOne D 𝔪 k⁻¹ := congOne_inv hk hcong
  set K : Matrix (Fin a) (Fin a) (AE D) := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  set T : Matrix (Fin d) (Fin a) (AE D) := z.map (inc D) * (K - 1) with hT
  have hTmem : ∀ i j, T i j ∈ hatId D 𝔪 := by
    intro i j
    rw [hT, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    obtain ⟨b, hb⟩ := ‹∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)› i l
    rw [Matrix.map_apply, hb]
    exact mul_mem_hatId D 𝔪 _ (inc_mem_OhE D b) _ (hinv l j)
  choose b hb y hy hby using fun i j => exists_mem_approx D 𝔪 m hm (T i j) (hTmem i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have hKinv : (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = K := by
    rw [hK, Subgroup.coe_inv]
  have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
  have hzK : z.map (inc D) * K = z.map (inc D) + T := by
    rw [hT, Matrix.mul_sub, Matrix.mul_one]; abel
  have key : ∀ i j, ((z + Matrix.of fun i j => (b i j : D.host.E)).map (inc D) -
      (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * z.map (inc D) *
        (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j =
      inc D (b i j : D.host.E) - T i j := by
    intro i j
    rw [e1, Matrix.one_mul, hKinv, hzK, Matrix.map_add _ (map_add (inc D))]
    simp [Matrix.map_apply]
  unfold CloseTo
  exact fun i j => ⟨y i j, hy i j, (key i j).trans (hby i j)⟩

end GlobalTheory.CongApprox
end

