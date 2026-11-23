module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceEqRangeFockMapVariableSignatu
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.PolRangeD

open GlobalTheory.RealLift.PolRangePf

theorem tensD_top {ι : Type} [Fintype ι] [DecidableEq ι] {σ : ι → Type}
    (N : Submodule ℂ (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : MvPolynomial (σ w) ℂ)) ∈ N)
    (hX : ∀ (w : ι) (l : σ w), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial (σ w) ℂ)) T ∈ N) :
    N = ⊤ := by
  have key : ∀ s : Finset ι, ∀ f : ∀ w, MvPolynomial (σ w) ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun w => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial (σ w₀) ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : (∀ w : ι, MvPolynomial (σ w) ℂ) →ₘₗ[ℂ]
          (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial (σ w₀) ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ w₀), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [GlobalTheory.RealLift.atPl_tprod] at this
        simpa using this
      have htop := GlobalTheory.RealLift.mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

theorem tensD_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (N : Submodule ℂ (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w) c) T ∈ N) : N = ⊤ := by
  refine tensD_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

theorem sumPlD_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))
      = Complex.I • sumPl (fun w => heisOp (c w))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, GlobalTheory.RealLift.atPl_tprod, GlobalTheory.RealLift.heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

theorem polRangeD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (P Q R S : InfinitePlace F → ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm (P w) (Q w)) →
    (∀ w, W.θ w * C w = C w * Jm (R w) (S w)) → IsFockMapD ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hL := GlobalTheory.RealLift.actsLaws
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (e : ℂ),
      A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm (R w) (S w) * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ
          = e • ((A w * Jm (P w) (Q w)) * c * (Jm (R w) (S w) * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm (P w) (Q w) * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm (R w) (S w))) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPlD_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tensD_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update
          (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w')) T = atPl w (heisOp c) T := by
        rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
        · simp
        · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
        · simp
      have := pol_der u hu _ hT _ (der u hu _ hu' T)
      rwa [hs] at this
    have : T ∈ (M.Pol ψ τ).comap Φ := htop ▸ Submodule.mem_top
    exact this
  · unfold Model.Pol
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
    · obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := GlobalTheory.T.fock_vacuum_line_placewise_signatures F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end GlobalTheory.HoweD.PolRangeD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumTrivSqZeroExtEq
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS.FunDer

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TangentOrigin GlobalTheory.Frames GlobalTheory.FlagTan
open TrivSqZeroExt hiding map lift
open scoped Classical

theorem primeSpectrum_trivSqZeroExt_eq {L ι : Type} [Field L] (x y : PrimeSpectrum (TrivSqZeroExt L (ι → L))) :
    x = y := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt L (ι → L)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem primeSpectrum_field_eq {L : Type} [Field L] (x y : PrimeSpectrum L) : x = y :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)

theorem le_preimage_of_unique {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R']
    (hR : ∀ x y : PrimeSpectrum R, x = y) {T : Scheme.{0}} (φ : R →+* R') (x : Sp R ⟶ T) (V : T.Opens)
    (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint R') = s := hR _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint R') ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem top_le_comp {S T U : Scheme.{0}} (f : S ⟶ T) (x : T ⟶ U) (V : U.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ (f ≫ x) ⁻¹ᵁ V := fun s _ => h (Set.mem_univ (f s))

theorem top_le_of_red {L R : Type} [Field L] [CommRing R] (hR : ∀ x y : PrimeSpectrum R, x = y) (ρ : R →+* L)
    {T : Scheme.{0}} {p : Sp R ⟶ T} {z : Sp L ⟶ T} (e : spMap ρ ≫ p = z) {O : T.Opens} (h : ⊤ ≤ z ⁻¹ᵁ O) :
    ⊤ ≤ p ⁻¹ᵁ O :=
  le_preimage_of_unique hR ρ p O (e ▸ h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem lift_eq {S : Scheme.{0}} {a b : S ⟶ M.X} (h : a ≫ toFlag M = b ≫ toFlag M) (ha : ⊤ ≤ a ⁻¹ᵁ M.off) :
    a = b := by
  have hU : ⊤ ≤ (a ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ha (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have e : a ≫ M.σ = b ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, Category.assoc]
    exact h
  exact (M.existsUnique_lift (a ≫ M.σ) hU).unique rfl e.symm

theorem exists_lift_of_unique {L R : Type} [Field L] [Algebra c.F L] [CommRing R] [Algebra c.F R]
    (hR : ∀ x y : PrimeSpectrum R, x = y) (ρ : R →ₐ[c.F] L) {Q : FrPt Xo c L} {W : FrPt Xo c R} (hd : FrMap ρ W Q)
    {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ ZW : Sp R ⟶ M.X, ZW ≫ toFlag M = X.ptY W ∧ spMap ρ.toRingHom ≫ ZW = z := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY W ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_unique hR ρ.toRingHom _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY W) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY W := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap ρ.toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_unique hR ρ.toRingHom _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap ρ.toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, hred⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

theorem red_eq {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {z : Sp L ⟶ M.X}
    (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {R : Type} [CommRing R] [Algebra c.F R]
    {ρ : R →ₐ[c.F] L} {u : FrPt Xo c R} (hu : FrMap ρ u Q) {p : Sp R ⟶ M.X} (hp : p ≫ toFlag M = X.ptY u) :
    spMap ρ.toRingHom ≫ p = z :=
  (lift_eq M (by rw [Category.assoc, hp, X.ptY_frMap hu, hz]) ho).symm

variable {K : Type} [Field K] [Algebra c.F K]

theorem der_dir {ι : Type} [Fintype ι] {Q : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q)
    (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {W : FrPt Xo c (TrivSqZeroExt K (ι → K))} (hW : FrMap (fstHom c.F K (ι → K)) W Q) :
    ∃ ZW : Sp (TrivSqZeroExt K (ι → K)) ⟶ M.X, ∀ (m : ι → K) (u : FrPt Xo c (DualNumber K))
      (p : Sp (DualNumber K) ⟶ M.X), FrMap (dir c m) W u → p ≫ toFlag M = X.ptY u →
      ∀ (O : M.X.Opens) (g : Γ(M.X, O)) (hp : ⊤ ≤ p ⁻¹ᵁ O), ∃ hZ : ⊤ ≤ ZW ⁻¹ᵁ O,
        (evalPt p O hp g).snd = ∑ k, (evalPt ZW O hZ g).snd k * m k := by
  obtain ⟨ZW, h1, h2⟩ := exists_lift_of_unique M primeSpectrum_trivSqZeroExt_eq _ hW hz ho
  have hZo : ⊤ ≤ ZW ⁻¹ᵁ M.off := top_le_of_red primeSpectrum_trivSqZeroExt_eq _ h2 ho
  refine ⟨ZW, fun m u p hu hp O g hpO => ?_⟩
  have e : p = spMap (dir c m).toRingHom ≫ ZW :=
    (lift_eq M (by rw [Category.assoc, h1, X.ptY_frMap hu, hp]) (top_le_comp _ _ _ hZo)).symm
  subst e
  have hZ : ⊤ ≤ ZW ⁻¹ᵁ O := le_preimage_of_unique primeSpectrum_trivSqZeroExt_eq _ ZW O hpO
  refine ⟨hZ, ?_⟩
  rw [evalPt_spMap_comp _ ZW O hZ hpO]
  exact snd_dir m _

theorem der_vert_eq_zero {y : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY y) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {N : FIx Dw → K} {u : FrPt Xo c (DualNumber K)} (h : IsVert y N u)
    (hN : ∀ σ i j, i < j → N (some ⟨σ, i, j⟩) = 0) {p : Sp (DualNumber K) ⟶ M.X} (hp : p ≫ toFlag M = X.ptY u)
    (O : M.X.Opens) (g : Γ(M.X, O)) (h1 : ⊤ ≤ p ⁻¹ᵁ O) : (evalPt p O h1 g).snd = 0 := by
  obtain ⟨y₀, h₀, hs⟩ := h
  have hb : FrBor (fun k => oneAddEps (Multiplicative.ofAdd (diagOf N k))) y₀ u :=
    (frBor_iff_frChg _ _ _).2 ⟨unip K N, fun σ i j hij => by simp [unip, hN σ i j hij, hij.ne],
      fun _ _ => by simp [unip, oneAddEps, diagOf], hs⟩
  have e : p = spMap (cst c K).toRingHom ≫ z := by
    refine (lift_eq M ?_ (top_le_comp _ _ _ ho)).symm
    rw [Category.assoc, hz, X.ptY_frMap h₀, X.ptY_frBor hb, hp]
  subst e
  have hzO : ⊤ ≤ z ⁻¹ᵁ O := le_preimage_of_unique primeSpectrum_field_eq _ z O h1
  rw [evalPt_spMap_comp _ z O hzO h1]
  rfl

theorem der_shift {y : FrPt Xo c K} {z : Sp K ⟶ M.X} (hz : z ≫ toFlag M = X.ptY y) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {N : FIx Dw → K} {v v' : FrPt Xo c (DualNumber K)} (h : IsDef y v) (h' : IsShift N v v')
    {zz : FIx Dw → FrPt Xo c (DualNumber K)} (hzz : ∀ k, IsVert y (Pi.single k (1 : K)) (zz k))
    {p p' : Sp (DualNumber K) ⟶ M.X} {q : FIx Dw → (Sp (DualNumber K) ⟶ M.X)} (hp : p ≫ toFlag M = X.ptY v)
    (hp' : p' ≫ toFlag M = X.ptY v') (hq : ∀ k, q k ≫ toFlag M = X.ptY (zz k)) (O : M.X.Opens) (g : Γ(M.X, O))
    (h1 : ⊤ ≤ p ⁻¹ᵁ O) (h2 : ⊤ ≤ p' ⁻¹ᵁ O) (h3 : ∀ k, ⊤ ≤ q k ⁻¹ᵁ O) :
    (evalPt p' O h2 g).snd = (evalPt p O h1 g).snd + ∑ k, N k * (evalPt (q k) O (h3 k) g).snd := by
  let emb : DualNumber K →ₐ[c.F] TrivSqZeroExt K (Option (FIx Dw) → K) :=
    (TrivSqZeroExt.map (LinearMap.single K (fun _ : Option (FIx Dw) => K) none)).restrictScalars c.F
  have e1 : ∀ a, (emb a).fst = a.fst := fun a => fst_map _ a
  have e2 : ∀ a, (emb a).snd = Pi.single none a.snd := fun a => snd_map _ a
  obtain ⟨W₀, hW₀⟩ := exists_frMap emb v
  let n : FIx Dw → Option (FIx Dw) → K := fun k => Pi.single (some k) 1
  obtain ⟨W, hW, -⟩ := existsUnique_frChg E H Dw l Xo c _ W₀ _ (isUnit_unip₀ (K := K) n).unit (isUnit_det_unip n)
  have key : ∀ (m : Option (FIx Dw) → K) (z₀ z : FrPt Xo c (DualNumber K)), FrMap (dir c m) W₀ z₀ →
      IsShift (fun k => m (some k)) z₀ z → FrMap (dir c m) W z := fun m z₀ z k₀ k => by
    refine (frMap_iff_frChg hW k₀).2 ?_
    unfold IsShift at k
    convert k using 2 with τ
    · ext i j <;> simp [unip, n, Pi.single_apply]
    · ext <;> simp [unip₀, n, Pi.single_apply]
  have k1 : ∀ m : Option (FIx Dw) → K, m none = 1 → FrMap (dir c m) W₀ v := fun m hm =>
    frMap_of_comp hW₀ (frMap_id v) fun a => by ext <;> simp [e1, e2, Pi.single_apply, hm]
  have kv : FrMap (dir c (Pi.single none 1)) W v :=
    key _ v v (k1 _ (by simp)) (by convert isShift_zero v using 2; simp)
  have hWy : FrMap (fstHom c.F K (Option (FIx Dw) → K)) W y := frMap_comp kv h fun a => by simp
  obtain ⟨ZW, hZW⟩ := der_dir M hz ho hWy
  obtain ⟨hZ1, a1⟩ := hZW _ _ p' (key (fun k => k.elim 1 N) v v' (k1 _ rfl) h') hp' O g h2
  obtain ⟨hZ2, a2⟩ := hZW _ _ p kv hp O g h1
  rw [a1, a2, Fintype.sum_option]
  congr 1
  · simp [Pi.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨y₀, h₀, hk⟩ := hzz k
  obtain ⟨hZ3, a3⟩ := hZW _ _ (q k) (key (Pi.single (some k) 1) y₀ (zz k)
    (frMap_of_comp hW₀ (frMap_comp (χ := (cst c K).comp (red c K)) h h₀ fun _ => rfl) fun a => by
      ext <;> simp [e1, e2, Pi.single_apply]) (by
      convert hk using 2; simp [Pi.single_apply])) (hq k) O g (h3 k)
  rw [a3]
  simp [Pi.single_apply, mul_comm]

theorem evalPt_eq_of_eq {R : Type} [CommRing R] {T : Scheme.{0}} {a b : Sp R ⟶ T} (e : a = b) (O : T.Opens)
    (ha : ⊤ ≤ a ⁻¹ᵁ O) (hb : ⊤ ≤ b ⁻¹ᵁ O) (g : Γ(T, O)) : evalPt a O ha g = evalPt b O hb g := by
  subst e
  rfl

end GlobalTheory.CompHS.FunDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidDescendsFieldMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

theorem GlobalTheory.Nef.RatRigidField.spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

namespace GlobalTheory.Nef

theorem isRatPath_map {F Ω : Type} [Field F] [Field Ω] (φ : F →+* Ω) {Y : Scheme.{0}}
    (ξ : Sp (PowerSeries F) ⟶ Y) (h : IsRatPath ξ) : IsRatPath (spMap (PowerSeries.map φ) ≫ ξ) := by
  obtain ⟨β, hβ⟩ := h
  have hinjP : Function.Injective
      ((algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ)) :=
    (IsFractionRing.injective (PowerSeries Ω) (LaurentSeries Ω)).comp
      (PowerSeries.map_injective φ φ.injective)
  have hinjR : Function.Injective
      ((algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ)) :=
    (IsFractionRing.injective (Polynomial Ω) (RatFunc Ω)).comp
      (Polynomial.map_injective φ φ.injective)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LaurentSeries F →+* LaurentSeries Ω, ψ.comp (algebraMap (PowerSeries F) (LaurentSeries F)) =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp (PowerSeries.map φ) :=
    by
    refine ⟨IsFractionRing.lift hinjP, ?_⟩
    ext1 x
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  obtain ⟨ρ, hρ0⟩ : ∃ ρ : RatFunc F →+* RatFunc Ω, ρ.comp (algebraMap (Polynomial F) (RatFunc F)) =
      (algebraMap (Polynomial Ω) (RatFunc Ω)).comp (Polynomial.mapRingHom φ) :=
    by
    refine ⟨IsFractionRing.lift hinjR, RingHom.ext fun x => ?_⟩
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  have hpol : ((algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ).comp (algebraMap (Polynomial F) (RatFunc F)) =
      (ψ.comp (algebraMap (RatFunc F) (LaurentSeries F))).comp (algebraMap (Polynomial F) (RatFunc F)) := by
    refine RingHom.ext fun p => ?_
    have h1 : ρ (algebraMap (Polynomial F) (RatFunc F) p) =
        algebraMap (Polynomial Ω) (RatFunc Ω) (p.map φ) := by
      have := congrArg (fun f => f p) hρ0
      simpa using this
    have h2 : ψ (algebraMap (PowerSeries F) (LaurentSeries F) (p : PowerSeries F)) =
        algebraMap (PowerSeries Ω) (LaurentSeries Ω) (PowerSeries.map φ (p : PowerSeries F)) :=
      congrArg (fun f => f (p : PowerSeries F)) hψ
    have h3 : PowerSeries.map φ (p : PowerSeries F) = ((p.map φ : Polynomial Ω) : PowerSeries Ω) := by
      ext n; simp [Polynomial.coeff_map]
    have hc : ∀ (K : Type) [Field K] (q : Polynomial K),
        algebraMap (RatFunc K) (LaurentSeries K) (algebraMap (Polynomial K) (RatFunc K) q) =
          algebraMap (PowerSeries K) (LaurentSeries K) (q : PowerSeries K) :=
      fun K _ q => (RatFunc.coe_coe q).symm
    simp only [RingHom.comp_apply]
    rw [h1, hc, hc, h2, h3]
  have hρ : (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp ρ =
      ψ.comp (algebraMap (RatFunc F) (LaurentSeries F)) :=
    IsLocalization.ringHom_ext (M := nonZeroDivisors (Polynomial F)) (S := RatFunc F) hpol
  refine ⟨spMap ρ ≫ β, ?_⟩
  have e1 : spMap (algebraMap (RatFunc Ω) (LaurentSeries Ω)) ≫ spMap ρ =
      spMap ψ ≫ spMap (algebraMap (RatFunc F) (LaurentSeries F)) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hρ]
  have e2 : spMap ψ ≫ spMap (algebraMap (PowerSeries F) (LaurentSeries F)) =
      spMap (algebraMap (PowerSeries Ω) (LaurentSeries Ω)) ≫ spMap (PowerSeries.map φ) := by
    rw [← RatRigidField.spMap_comp, ← RatRigidField.spMap_comp, hψ]
  rw [← Category.assoc, e1, Category.assoc, hβ, ← Category.assoc, e2, Category.assoc]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem ratRigid_of_field_map (S : Scheme.{0}) (G : Over S) [GrpObj G] (F Ω : Type) [Field F] [Field Ω]
    (φ : F →+* Ω) (b : Sp F ⟶ S) (h : RatRigid G (spMap φ ≫ b)) : RatRigid G b := by
  intro ξ hξ hr
  have hp := ((_root_.GlobalTheory.Nef.paths_bc).1 S G F Ω φ 2 1 b ξ hξ).1
  rw [PowerSeries.rescale_one, RingHom.id_comp, map_ofNat] at hp
  have e := h _ hp (isRatPath_map φ ξ hr)
  have hC : (PowerSeries.map φ).comp (PowerSeries.C (R := F)) = (PowerSeries.C (R := Ω)).comp φ := by
    ext1 x; simp
  have ht : spMap (PowerSeries.map φ) ≫ triv G b = triv G (spMap φ ≫ b) := by
    simp only [triv]
    rw [← Category.assoc, ← RatRigidField.spMap_comp, hC, RatRigidField.spMap_comp]
    simp only [Category.assoc]
  exact (_root_.GlobalTheory.Nef.spMap_injective_cancel).1 _ _ (PowerSeries.map φ) (PowerSeries.map_injective φ φ.injective) _ _ _
    (e.trans ht.symm)

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def SquareStanding (G : GridData L sc) (t : T) : Prop :=
  11 ≤ D.host.splitBound ∧
    ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal

end GlobalTheory.FunObj

end
end

