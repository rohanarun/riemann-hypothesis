module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRational
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT

theorem natCast_smul_eq_ring {E : Type} [Field E] [NumberField E] {a b : ℕ} (n : ℕ) (y : HomE E a b) :
    (n : 𝓞 E) • y = (n : E) • y := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem natCast_smul_mem {E : Type} [Field E] [NumberField E] {a b : ℕ} (M : Submodule (𝓞 E) (HomE E a b)) (n : ℕ)
    {y : HomE E a b} (hy : y ∈ M) : (n : E) • y ∈ M := by
  rw [← natCast_smul_eq_ring]; exact M.smul_mem _ hy

theorem exists_lift_halfAO : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  intro X A a b S N N' cA c hfg hne _ hU hN hN' hcA hc x hx
  obtain ⟨-, hfull, -, hloc⟩ := _root_.GlobalTheory.MomT.LatFin.per_lattice_facts X A a b N N' hfg hne hN hN'
  have hF : GlobalTheory.ThetaMove.Full (per A N N') := fun y => by
    obtain ⟨n, hn, hy⟩ := hfull y
    exact ⟨n, hn, by rwa [natCast_smul_eq_ring]⟩
  have hD : ((cA * c : ℕ) : X.E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hcA hc).ne'
  obtain ⟨t, h1, h2⟩ := hF.approx S (((cA * c : ℕ) : X.E)⁻¹ • x)
  have hx' : (cA : X.E) • x ∈ homAt S N N' := by
    rw [← natCast_smul_eq_ring]; exact hx
  refine ⟨((cA * c : ℕ) : X.E) • t, ?_, (cA : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x), ?_, ?_⟩
  · unfold halfAO twist₂
    rw [Submodule.mem_iInf]
    intro Q
    rw [Submodule.mem_comap]
    change ((((cA * c : ℕ) : X.E) ^ (-expS S Q))⁻¹ • ((cA * c : ℕ) : X.E) • t) ∈ _
    unfold expS
    split_ifs with hQ hQ'
    · have e : ((((cA * c : ℕ) : X.E) ^ (-(1 : ℤ)))⁻¹ • ((cA * c : ℕ) : X.E) • t) =
          ((cA * c : ℕ) : X.E) • ((cA * c : ℕ) : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x) + (c : X.E) • (cA : X.E) • x := by
        rw [smul_sub, smul_inv_smul₀ hD, smul_sub, zpow_neg, inv_inv, zpow_one, smul_smul (c : X.E), mul_comm (c : X.E),
          ← Nat.cast_mul, sub_add_cancel]
      rw [e]
      exact add_mem (natCast_smul_mem _ _ (natCast_smul_mem _ _ (h1 Q hQ)))
        (natCast_smul_mem _ _ ((hloc Q (hU Q hQ) _).2 (hx' Q hQ)))
    · rw [neg_neg, zpow_one, inv_smul_smul₀ hD]
      exact h2 Q hQ
    · rw [neg_zero, zpow_zero, inv_one, one_smul]
      exact natCast_smul_mem _ _ (h2 Q hQ)
  · intro P hP
    exact (hloc P (hU P hP) _).1 (natCast_smul_mem _ _ (h1 P hP))
  · change (c : 𝓞 X.E) • (cA : X.E) • (t - ((cA * c : ℕ) : X.E)⁻¹ • x) = _
    rw [natCast_smul_eq_ring, smul_smul, mul_comm (c : X.E), ← Nat.cast_mul, smul_sub, smul_inv_smul₀ hD]

end GlobalTheory.MomT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRealAdelicHermitianSignatureCoordinates
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.RealSpaceCoord

theorem herm_eq_dot {P Q : ℕ} (x y : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm y x = star x ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ y) := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, Fintype.sum_sum_type, dotProduct, fromBlocks_mulVec, neg_mulVec,
    mul_comm]

theorem form_eq {M P Q : ℕ} (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (x y : Fin M → ℂ) :
    ∑ i, ∑ j, star (x i) * (Aᴴ * Formalism.UG.Jpq P Q * A) i j * y j = ActionCoordinates.herm (A *ᵥ y) (A *ᵥ x) := by
  rw [herm_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (T : Type) [Fintype T] (τ : T → (E →+* ℂ)) (θ : T → (Ainf F ⊗[F] E →+* ℂ)), (Function.Bijective fun ρ => InfinitePlace.mk (τ ρ)) → (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), P + Q = M → ∀ J : Matrix (Fin M) (Fin M) E, IsHermND σ J → ∀ A : T → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ, (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∃ e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (T → ActionCoordinates.Wsp P Q), (∀ X ρ, e X ρ = A ρ *ᵥ fun i => θ ρ (X 0 i)) ∧ ∀ X Y ρ, θ ρ (hR (Ainf F) σ J (X 0) (Y 0)) = ActionCoordinates.herm (e Y ρ) (e X ρ) := by
  intro F E _ _ _ _ _ σ h T _ τ θ hτ hθ M P Q hM J hJ A hA
  obtain ⟨e0, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ T τ θ h hτ hθ
  let B : T → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ := fun ρ => (J.map (τ ρ))⁻¹ * ((A ρ)ᴴ * Formalism.UG.Jpq P Q)
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => by
    have hd : (J.map (τ ρ)).det = τ ρ J.det := ((τ ρ).map_det J).symm
    simp only [B]
    rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul]
    rw [hd]
    exact ((map_ne_zero (τ ρ)).2 hJ.2).isUnit
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ =>
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hM])).2 (hBA ρ)
  have he' : ∀ z ρ, θ ρ (e0.symm z) = z ρ := fun z ρ => by rw [← he, e0.apply_symm_apply]
  refine ⟨{ toFun := fun X ρ => A ρ *ᵥ fun i => θ ρ (X 0 i)
            invFun := fun z _ i => e0.symm fun ρ => (B ρ *ᵥ z ρ) i
            left_inv := fun X => ?_
            right_inv := fun z => ?_
            map_add' := fun X Y => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ => rfl, fun X Y ρ => ?_⟩
  · funext k i
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [mulVec_mulVec, hBA, one_mulVec]
    rw [RingEquiv.symm_apply_eq]
    funext ρ
    rw [he]
  · funext ρ
    simp only [he']
    rw [mulVec_mulVec, hAB, one_mulVec]
  · funext ρ
    refine Eq.trans ?_ (mulVec_add (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    congr 1
    funext i
    exact map_add (θ ρ) _ _
  · refine continuous_pi fun ρ => continuous_const.matrix_mulVec (continuous_pi fun i => ?_)
    simp only [← he]
    exact (continuous_apply ρ).comp (hc.comp ((continuous_apply i).comp (continuous_apply 0)))
  · exact continuous_pi fun _ => continuous_pi fun i => hc'.comp (continuous_pi fun ρ =>
      (continuous_apply i).comp (continuous_const.matrix_mulVec (continuous_apply ρ)))
  · refine Eq.trans ?_ (form_eq (A ρ) (fun i => θ ρ (X 0 i)) (fun i => θ ρ (Y 0 i)))
    rw [hA]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Mem.VolInfIso.infEmb_sigR σ (τ ρ) (θ ρ) h (hθ ρ)]
    congr 2
    exact (hθ ρ).1 _

end GlobalTheory.RealSpaceCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
section
noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.PeriodClassSum
open scoped Matrix ComplexOrder

theorem wForm_sum {C ι κ : Type} [Fintype C] [Fintype ι] [Fintype κ] (w : C → ℕ) (G : Matrix ι ι ℂ) (u : κ → C → ι → ℂ)
    (a b : κ → ℂ) : star a ⬝ᵥ (Matrix.of fun i j => wForm w G (u i) (u j)) *ᵥ b = wForm w G (∑ i, a i • u i) (∑ i, b i • u i) := by
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  simp only [wForm, Finset.sum_apply, Pi.smul_apply, star_sum, star_smul, sum_dotProduct, smul_dotProduct,
    Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K]


omit [NumberField K] in
theorem map_pair {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (p : V →ₗ⋆[K] V →ₗ[K] K)
    (φ : K →+* ℂ) (x y : V) (hx : ∀ i, b.repr x i ∈ cmMax K) :
    φ (p x y) = star (fun i => φ (b.repr x i)) ⬝ᵥ (Matrix.of fun i j => p (b i) (b j)).map φ *ᵥ fun i => φ (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, dotProduct,
    Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum, RingHom.id_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, hx i φ, starRingEnd_apply]
  ring

variable (S : CSD K) (v : InfinitePlace K)

def coAt (f : S.Cl → S.V) : S.Cl → S.ιV → ℂ := fun c i => v.embedding (S.bV.repr (f c) i)

theorem coAt_sum (x : S.Forms) :
    coAt S v (x : S.Cl → S.V) = ∑ i, v.embedding (S.basis.repr x i) • coAt S v (S.basis i : S.Cl → S.V) := by
  funext c k
  conv_lhs => rw [← S.basis.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coAt, AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smul, smul_eq_mul]
  simp

theorem coAt_indep : LinearIndependent ℂ fun i => fun p : S.Cl × S.ιV => coAt S v (S.basis i : S.Cl → S.V) p.1 p.2 := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  let f : S.Forms →ₗ[K] (S.Cl × S.ιV → K) := LinearMap.pi fun p =>
    S.bV.coord p.2 ∘ₗ LinearMap.proj p.1 ∘ₗ S.Forms.subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext c
    exact S.bV.forall_coord_eq_zero_iff.1 fun k => congrFun hφ (c, k)
  exact (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (S.basis.linearIndependent.map' f hf)

theorem H_map (hb : S.HasRatBasis) : S.H.map v.embedding = Matrix.of fun i j =>
    wForm S.wt (S.gramV.map v.embedding) (coAt S v (S.basis i : S.Cl → S.V)) (coAt S v (S.basis j : S.Cl → S.V)) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, wForm, map_sum, map_mul, map_inv₀, map_natCast]
  exact Finset.sum_congr rfl fun c _ => congrArg _ (map_pair S.bV S.pair v.embedding _ _ (S.basis_rat hb i c))

theorem H_posDef (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) : (S.H.map v.embedding).PosDef := by
  rw [H_map S v hb]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    exact wForm_conj _ hG.1 _ _
  · rw [wForm_sum]
    refine lt_of_le_of_ne (wForm_nonneg _ hG.posSemidef _) fun h0 => ha ?_
    have h1 := wForm_eq_zero _ S.wt_pos hG h0.symm
    funext i
    refine Fintype.linearIndependent_iff.1 (coAt_indep S v) a ?_ i
    funext p
    simpa using congrFun (congrFun h1 p.1) p.2

theorem normAt_sq (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) (x : S.Forms) :
    ((Formalism.HermitianLatticesTheory.normAt S.basis (stdFrame S.H) v x ^ 2 : ℝ) : ℂ) =
      wForm S.wt (S.gramV.map v.embedding) (coAt S v (x : S.Cl → S.V)) (coAt S v (x : S.Cl → S.V)) := by
  have hm := (frameOfSpec _ _ (H_posDef S v hb hG)).2
  have h1 := wForm_sum S.wt (S.gramV.map v.embedding) (fun i => coAt S v (S.basis i : S.Cl → S.V))
    (Formalism.HermitianLatticesTheory.vecAt S.basis v x) (Formalism.HermitianLatticesTheory.vecAt S.basis v x)
  rw [← H_map S v hb, ← hm, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h1
  rw [coAt_sum S v x]
  refine Eq.trans ?_ h1
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

variable (T : GSD K) (h : T.Ok) (hr : ∀ (g : T.G) i j, T.bV.repr (T.ρ g (T.bV j)) i ∈ cmMax K)


include hr in
theorem isFormsOf_toH (hG : ∀ v : InfinitePlace K, (T.gramV.map v.embedding).PosDef) (N : Submodule (𝓞 K) T.EqFun) :
    IsFormsOf T h N (T.toH h N) (LinearEquiv.refl _ _) := by
  refine ⟨fun _ => Iff.rfl, fun v (x : T.EqFun) => ?_⟩
  exact (normAt_sq (T.toCSD h) v (FormsDescent.hasRatBasis_of_act _ fun c γ => hr γ.1) (hG v) (T.res h x)).trans
    (ipAt_eq T h v x x).symm


include h hr in
theorem pairAt_rho (g : T.G) (x : T.V) : T.pairAt v (T.ρ g x) (T.ρ g x) = T.pairAt v x x := by
  let u : T.ιV → Unit → T.ιV → ℂ := fun k _ i => v.embedding (T.bV.repr (T.ρ g (T.bV k)) i)
  have h1 := wForm_sum (fun _ => 1) (T.gramV.map v.embedding) u (fun i => v.embedding (T.bV.repr x i))
    (fun i => v.embedding (T.bV.repr x i))
  have e1 : (Matrix.of fun i j => wForm (fun _ => 1) (T.gramV.map v.embedding) (u i) (u j)) = T.gramV.map v.embedding := by
    ext i j
    simp only [Matrix.of_apply, wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]
    refine (map_pair T.bV T.pair v.embedding _ _ fun k => hr g k i).symm.trans ?_
    rw [h.inv]
    rfl
  have e2 : (∑ i, v.embedding (T.bV.repr x i) • u i) = fun _ i => v.embedding (T.bV.repr (T.ρ g x) i) := by
    funext c k
    conv_rhs => rw [← T.bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, smul_eq_mul]
    simp
  rw [e1, e2] at h1
  rw [pairAt_eq, pairAt_eq, h1]
  simp only [wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]


end Metric

end GlobalTheory.PeriodOnStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsTranslateRationalPointUnitDenominator
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.UnitTr

theorem lamC_mul_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left (mul_mem hx hy), ← map_mul]
  rfl

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem coc_nat_left (n : ℕ) (x y : HomE X.E a b) : coc A ((n : X.E) • x) y = n * coc A x y := by
  have h := (_root_.GlobalTheory.MomT.Heis.calculus X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h 0 0 y).1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).1, ih]; push_cast; ring

theorem coc_nat_right (n : ℕ) (x y : HomE X.E a b) : coc A x ((n : X.E) • y) = n * coc A x y := by
  have h := (_root_.GlobalTheory.MomT.Heis.calculus X A a b).2.2.2.1
  induction n with
  | zero =>
    have := (h x 0 0).2.1
    simp only [add_zero] at this
    simp only [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, (h _ _ _).2.1, ih]; push_cast; ring

theorem coc_rat (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hX : X.Ok) (hL : A.LaHyp a b ∅)
    (hA : A.AA ≠ ⊥) (hN : IsSdLat N) (hN' : IsSdLat N') (x y : HomE X.E a b) : ∃ r : ℚ, coc A x y = (r : ℝ) := by
  obtain ⟨hδ, -, -, -, hFG, hLa⟩ := hL
  have hfull := (_root_.GlobalTheory.MomT.LatFin.per_lattice_facts X A a b N N' hFG hA hN hN').2.1
  have hint := (_root_.GlobalTheory.MomT.CocInt.cocycle_integral X A a b N N' hX hδ (hLa N N' hN hN').2).2.2
  obtain ⟨n, hn, hx⟩ := hfull x
  obtain ⟨n', hn', hy⟩ := hfull y
  obtain ⟨k, hk⟩ := hint ((n : X.E) • x) ((n' : X.E) • y) fun Q =>
    ⟨1, one_ne_zero, by simpa using le_locP Q _ hx, by simpa using le_locP (conjPrime₂ Q) _ hy⟩
  rw [coc_nat_left, coc_nat_right] at hk
  refine ⟨(k : ℚ) / (n * n'), ?_⟩
  have h1 : (n : ℝ) ≠ 0 := by positivity
  have h2 : (n' : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← hk]
  field_simp

theorem Wx_const_mul (x : HomE X.E a b) (c : ℂ) (F : VCx X.Tau a b → ℂ) :
    Wx A x (fun z => c * F z) = fun z => c * Wx A x F z := by
  funext z
  simp only [Wx, opU]
  ring

theorem Wx_per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hL : A.LaHyp a b ∅)
    (hN : IsSdLat N) (hN' : IsSdLat N') (l : HomE X.E a b) (hl : l ∈ per A N N') :
    Wx A l (A.e a b N N') = A.e a b N N' := by
  funext z
  exact (hL.2.2.2.2.2 N N' hN hN').1 (emb A l) ⟨l, hl, rfl⟩ z

theorem moments_unit_translate : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), X.Ok → A.LaHyp a b ∅ → A.AA ≠ ⊥ → A.ESmooth a b → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → ∀ (t : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * (ϖ : X.E)) • t ∈ per A N N' → (∀ m, jetC A.cD (Wx A t (A.e a b N N')) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure (per A N N' : Set (HomE X.E a b)) (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A t (A.e a b N N')) m) := by
  intro X A a b ϖ p N N' _ lam ι un hX hL hA hS hϖ hcop hN hN' hP t n hn ht
  have hp : p.Prime := Fact.out
  have hH := _root_.GlobalTheory.MomT.Heis.calculus X A a b
  have hroot := (_root_.GlobalTheory.MomPlace.places X.K p A.σ₀ ι).2.2 lam
  have hϖE : (ϖ : X.E) * star (ϖ : X.E) = (p : X.E) := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hϖ
    simpa [Fields.conjO, starRingEnd_apply] using this
  have hϖ0 : (ϖ : X.E) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hϖE
    exact hp.ne_zero (by exact_mod_cast hϖE.symm)
  have hbar : ((X.conjO ϖ : 𝓞 X.E) : X.E) = star (ϖ : X.E) := by
    simp [Fields.conjO, starRingEnd_apply]
  have hnϖ : IsCoprime (n : 𝓞 X.E) ϖ := by
    have h1 : IsCoprime (n : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hn
    rw [← hϖ] at h1
    exact h1.of_mul_right_left
  obtain ⟨α, β, hαβ⟩ := hnϖ.mul_left hcop.symm
  have hαβE : (α : X.E) * (n * star (ϖ : X.E)) + β * ϖ = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) hαβ
    simpa [hbar] using this
  have hsm : ∀ (r : 𝓞 X.E) (x : HomE X.E a b), x ∈ per A N N' → (r : X.E) • x ∈ per A N N' := fun r x hx =>
    Submodule.smul_mem _ r hx
  set t' : HomE X.E a b := ((β : X.E) * ϖ) • t with ht'
  have ht'M : (n : X.E) • t' ∈ per A N N' := by
    have := hsm β _ ht
    rw [smul_smul] at this
    rw [ht', smul_smul]
    convert this using 2
    ring
  obtain ⟨N₀, hN₀, hJ, hC⟩ := hP N N' hN hN' t' ⟨n, hn, ht'M⟩
  obtain ⟨α', β', h'⟩ : IsCoprime (N₀ : 𝓞 X.E) (p : 𝓞 X.E) := Nat.Coprime.cast hN₀
  have h'E : (α' : X.E) * N₀ + β' * (ϖ * star (ϖ : X.E)) = 1 := by
    have := congrArg (fun z : 𝓞 X.E => (z : X.E)) h'
    rw [hϖE]
    simpa using this
  set m₁ : HomE X.E a b := ((α' * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hm₁
  set l : HomE X.E a b := ((β' * X.conjO ϖ * X.conjO ϖ * α : 𝓞 X.E) : X.E) • (((n : X.E) * (ϖ : X.E)) • t) with hl
  have hm₁M : m₁ ∈ per A N N' := hsm _ _ ht
  have hlM : l ∈ per A N N' := hsm _ _ ht
  set y : HomE X.E a b := ((N₀ : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • m₁ with hy
  have hdec : y + (t' + l) = t := by
    rw [hy, hm₁, hl, ht']
    simp only [smul_smul, ← add_smul]
    conv_rhs => rw [← one_smul X.E t]
    congr 1
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at hbar hαβE h'E hϖ0 ⊢
    rw [hbar]
    field_simp
    linear_combination (α * n * star (ϖ : X.E)) * h'E + hαβE
  obtain ⟨r₁, hr₁⟩ := coc_rat A N N' hX hL hA hN hN' t' l
  obtain ⟨r₂, hr₂⟩ := coc_rat A N N' hX hL hA hN hN' y (t' + l)
  set ζ : ℂ := Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ)) with hζ
  have hkey : Wx A t (A.e a b N N') = fun z => ζ * Wx A y (Wx A t' (A.e a b N N')) z := by
    have e1 := hH.1 t' l (A.e a b N N')
    rw [Wx_per A N N' hL hN hN' l hlM] at e1
    rw [e1, Wx_const_mul, hH.1 y (t' + l), hdec, hr₁, hr₂]
    funext z
    rw [hζ, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    have : -(2 * (Real.pi : ℂ)) * Complex.I * (((-(r₁ + r₂) : ℚ) : ℝ) : ℂ) + -(2 * (Real.pi : ℂ)) * Complex.I * ((r₁ : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ)) * Complex.I * ((r₂ : ℝ) : ℂ) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, one_mul]
  have hjet : ∀ m, jetC A.cD (Wx A t (A.e a b N N')) m = ζ * jetC A.cD (Wx A y (Wx A t' (A.e a b N N'))) m := by
    intro m
    have := hH.2.2.2.2.2.2.2 Unit {()} (fun _ => ζ) (fun _ => Wx A y (Wx A t' (A.e a b N N')))
      (fun _ _ => hH.2.2.2.2.2.2.1 _ _ (hH.2.2.2.2.2.2.1 _ _ (hS N N' hN hN'))) m
    rw [hkey]
    simpa only [Finset.sum_singleton] using this
  have hζQ := hroot (-(r₁ + r₂))
  refine ⟨fun m => ?_, ?_⟩
  · rw [hjet]
    exact mul_mem hζQ.1 (hJ m₁ hm₁M m)
  · have hbrk : ∀ x, ‖TaylorLogMetric.lamC lam (brkE A y x)‖ = 1 := by
      intro x
      obtain ⟨s₁, hs₁⟩ := coc_rat A N N' hX hL hA hN hN' x y
      obtain ⟨s₂, hs₂⟩ := coc_rat A N N' hX hL hA hN hN' y x
      have := (hroot (s₁ - s₂)).2
      rw [hH.2.2.2.2.1, hH.2.2.1, hs₁, hs₂]
      rwa [Rat.cast_sub] at this
    have := clo_comb (Sup' := (per A N N' : Set (HomE X.E a b))) (tab' := ptTab ι un) (M' := Set.univ) hC ({()} : Finset Unit)
      (fun _ _ => TaylorLogMetric.lamC lam ζ) (fun _ m => (m₁, m)) (fun _ _ _ _ => hm₁M)
      (fun x => TaylorLogMetric.lamC lam ζ * TaylorLogMetric.lamC lam (brkE A y x))
      (fun x _ => by rw [norm_mul, hbrk, hζQ.2, one_mul]) (fun _ h h' => absurd h h')
      (fun x _ m _ => by simp only [Finset.sum_singleton]; rw [mul_assoc])
    refine clo_congr this subset_rfl subset_rfl fun m _ => ?_
    simp only [Finset.sum_singleton]
    rw [hjet, lamC_mul_of_mem lam hζQ.1 (hJ m₁ hm₁M m)]

end GlobalTheory.MomT.UnitTr
end
end

