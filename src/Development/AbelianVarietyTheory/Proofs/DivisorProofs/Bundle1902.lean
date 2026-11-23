module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoordLetterEquivApplyConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.SymFrame
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem const_of_periodic {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hp : (τ.map Complex.im).PosDef)
    {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hper : ∀ z M N, f (z + perV τ M N) = f z) (z w : Fin g → ℂ) :
    f z = f w := by
  let P : (Fin g → ℤ) × (Fin g → ℤ) →+ (Fin g → ℂ) := AddMonoidHom.mk' (fun a => perV τ a.1 a.2) fun a b => by
    have e : ∀ M N : Fin g → ℤ, cv (M + N) = cv M + cv N := fun M N => by ext i; simp [cv]
    simp only [perV, Prod.fst_add, Prod.snd_add, e, Matrix.mulVec_add]
    abel
  refine periodic_const_range P (eq_top_iff.2 fun v _ => ?_) f hf (fun z a => hper z a.1 a.2) z w
  obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hp.isUnit fun i => (v i).im
  let x : Fin g → ℝ := fun i => (v i).re - (τ.map Complex.re *ᵥ y) i
  have e : v = ∑ i, x i • P (Pi.single i 1, 0) + ∑ i, y i • P (0, Pi.single i 1) := by
    have c0 : cv (0 : Fin g → ℤ) = 0 := by ext i; simp [cv]
    have c1 : ∀ i : Fin g, cv (Pi.single i 1 : Fin g → ℤ) = Pi.single i 1 := fun i => by
      ext k; by_cases h : k = i <;> simp [cv, h, Pi.single_apply]
    ext k
    have hk := congrFun hy k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hk
    simp only [P, AddMonoidHom.mk'_apply, perV, c0, c1, Matrix.mulVec_zero, add_zero, zero_add, Matrix.mulVec_single_one,
      Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    apply Complex.ext
    · simp [x, Matrix.mulVec, dotProduct, mul_comm]
    · simp [← hk, mul_comm]
  rw [e]
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem autV_mul_autV {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) {a b : Fin g → ℂ} (ha : Half a) (hb : Half b)
    (M N : Fin g → ℤ) (z : Fin g → ℂ) : autV τ a b M N z * autV τ a b M N (-(z + perV τ M N)) = 1 := by
  have h : ∀ {c : Fin g → ℂ}, Half c → ∀ M : Fin g → ℤ, ∃ n : ℤ, 2 * (c ⬝ᵥ cv M) = n := fun {c} hc M => by
    classical
    refine ⟨∑ i, if c i = 0 then 0 else M i, ?_⟩
    rw [dotProduct, Finset.mul_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hc i with e | e <;> simp [e, cv]
  obtain ⟨m, hm⟩ := h ha M
  obtain ⟨n, hn⟩ := h hb N
  have hk : cv N ⬝ᵥ cv M = ((N ⬝ᵥ M : ℤ) : ℂ) := by simp [dotProduct, cv]
  rw [autV, autV, ← Complex.exp_add, Complex.exp_eq_one_iff]
  refine ⟨m - n + N ⬝ᵥ M, ?_⟩
  rw [dotProduct_neg, dotProduct_add, perV, dotProduct_add, hk]
  push_cast
  rw [← hm, ← hn]
  ring

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
  {ν : NumOf D ℂ N} {d : AB N.toNumB g}

theorem hol_base (G : Geo ν d) (U : D.P.A.left.Opens) (f : Γ(D.P.A.left, U)ˣ) :
    IsOpen {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ν.eA (d.ex z)).left U f.val) {z | ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ U} := by
  have e : ∀ z, ptB ν d z ≫ (snd (TF (R := R) ℂ) D.P.A).left = (ν.eA (d.ex z)).left := fun z => by
    rw [ptB, ← Over.comp_left, lift_snd]
  have h := G.hol ((snd (TF (R := R) ℂ) D.P.A).left ⁻¹ᵁ U) (pullU _ U f).val
  simp only [← e]
  refine ⟨h.1, h.2.congr fun z _ => ?_⟩
  exact (vtf_val_pullU (ptB ν d z) _ U f).symm

theorem differentiable_gen (G : Geo ν d) (hr : ν.rg ≠ 0) {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (ht : t.IsGen) (w : K → (Fin g → ℂ) → (Fin g → ℂ))
    (hw : ∀ k, Differentiable ℂ (w k)) (hφ : ∀ k z, (ν.eA (d.ex z)).left ≫ φ k = (ν.eA (d.ex (w k z))).left) :
    Differentiable ℂ fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k := by
  intro z₀
  let j : K → D.P.L.ι := fun k => ν.J ((ν.eA (d.ex z₀)).left ≫ φ k)
  obtain ⟨hS, hv⟩ := hol_base G (LB.wchart D.P.L φ j) (t.s j)
  have hJ : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((ν.eA (d.ex z)).left ≫ φ k) :=
    fun z q _ => Set.mem_iInter.2 fun k => ν.good ((ν.eA (d.ex z)).left ≫ φ k) (x := q) trivial
  have hk : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k,
      ⊤ ≤ (ν.eA (d.ex (w k z))).left ⁻¹ᵁ D.P.L.U (j k) := fun z hz k q _ => by
    rw [← hφ]
    exact Set.mem_iInter.1 (hz (x := q) trivial) k
  have hfr : ∀ z, ⊤ ≤ (ν.eA (d.ex z)).left ⁻¹ᵁ LB.wchart D.P.L φ j → ∀ k, (d.fr (w k z) : ℂ) * ν.rg =
      valF ((ν.eA (d.ex z)).left ≫ φ k) _ (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val * G.frG (j k) (w k z) :=
    fun z hz k => by
      rw [hφ, G.fr_eq]
      exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hk z hz k (x := q) trivial⟩
  have hne : ∀ k z, (d.fr (w k z) : ℂ) * ν.rg ≠ 0 := fun k z => mul_ne_zero (Units.ne_zero _) hr
  have hev : (fun z => vF t (ν.eA (d.ex z)).left ν.J / ∏ k, ((d.fr (w k z) : ℂ) * ν.rg) ^ ε k) =ᶠ[nhds z₀]
      fun z => valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val / ∏ k, G.frG (j k) (w k z) ^ ε k := by
    filter_upwards [hS.mem_nhds (hJ z₀)] with z hz
    have e : vF t (ν.eA (d.ex z)).left ν.J = (∏ k, valF ((ν.eA (d.ex z)).left ≫ φ k) _
        (D.P.L.g (ν.J ((ν.eA (d.ex z)).left ≫ φ k)) (j k)).val ^ ε k) *
        valF (ν.eA (d.ex z)).left (LB.wchart D.P.L φ j) (t.s j).val :=
      vtf_isGen_val D.P.L φ ε t ht _ _ j fun q _ => ⟨hJ z (x := q) trivial, hz (x := q) trivial⟩
    rw [e]
    simp only [hfr z hz, mul_zpow, Finset.prod_mul_distrib]
    refine mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ?_)
    exact left_ne_zero_of_mul (hfr z hz k ▸ hne k z)
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h0 : ∀ k, G.frG (j k) (w k z₀) ≠ 0 := fun k => right_ne_zero_of_mul (hfr z₀ (hJ z₀) k ▸ hne k z₀)
  have h1 : ∀ k, DifferentiableAt ℂ (fun z => G.frG (j k) (w k z)) z₀ := fun k =>
    ((G.fr_hol (j k)).differentiableAt ((hol_base G _ 1).1.mem_nhds (hk z₀ (hJ z₀) k))).comp z₀ (hw k z₀)
  have h2 : DifferentiableAt ℂ (fun z => ∏ k, G.frG (j k) (w k z) ^ ε k) z₀ :=
    by
      have hp : ∀ s : Finset K, DifferentiableAt ℂ (fun z => ∏ k ∈ s, G.frG (j k) (w k z) ^ ε k) z₀ := fun s => by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          simp only [Finset.prod_insert ha]
          exact ((h1 a).zpow (Or.inl (h0 a))).mul ih
      exact hp _
  simp only [div_eq_mul_inv]
  exact (hv.differentiableAt (hS.mem_nhds (hJ z₀))).mul
    (h2.inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h0 k)))

theorem rg_ne (ν : NumOf D ℂ N) : ν.rg ≠ 0 := by
  unfold NumOf.rg vF valF
  split_ifs with h
  · exact (((Units.isUnit _).map _).map _).ne_zero
  · exact (h fun q _ => Set.mem_iInter.2 fun _ => ν.good ((TF (R := R) ℂ).hom ≫ eSec D.P.A) (x := q) trivial).elim

end GlobalTheory.MBLow.Cl.SymFrame

namespace GlobalTheory.MBLow.Cl
open SymFrame

theorem sym_of_geo : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), Nonempty (Geo ν d) → d.Sym := by
  rintro R _ _ _ _ D - - _ N ν g d ⟨G⟩
  have hr := rg_ne ν
  have h0 : d.ex 0 = 1 := by simpa using d.ex_add 0 0
  have hneg : ∀ z, d.ex (-z) = (d.ex z)⁻¹ := fun z =>
    eq_inv_of_mul_eq_one_left (by rw [← d.ex_add, neg_add_cancel, h0])
  have hd := differentiable_gen G hr D.sym D.sym_gen ![fun z => -z, fun z => z]
    (fun k => by fin_cases k <;> simp <;> fun_prop) (fun k z => by
      fin_cases k
      · change _ ≫ (ι[D.P.A]).left = (ν.eA (d.ex (-z))).left
        rw [hneg, map_inv, Hom.inv_def, Over.comp_left]
      · exact Category.comp_id _)
  have hF : Differentiable ℂ fun z => (N.σ (d.ex z) : ℂ) * d.fr z / d.fr (-z) := by
    convert hd using 2 with z
    rw [ν.σ_eq, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, _root_.zpow_neg]
    have := (d.fr z).ne_zero
    have := (d.fr (-z)).ne_zero
    field_simp
  intro x
  have hc := const_of_periodic d.pos hF (fun z M M' => by
    have h1 := d.fr_per M M' z
    have h2 := d.fr_per M M' (-(z + perV d.τ M M'))
    have h3 := autV_mul_autV d.τ d.ha d.hb M M' z
    rw [show -(z + perV d.τ M M') + perV d.τ M M' = -z by abel] at h2
    rw [d.ex_add, (d.ker _).2 ⟨M, M', rfl⟩, _root_.mul_one, div_eq_div_iff (Units.ne_zero _) (Units.ne_zero _), h1, h2]
    linear_combination (-(N.σ (d.ex z) : ℂ) * d.fr (z + perV d.τ M M') * d.fr (-z)) * h3) x 0
  rw [h0, N.σ_one, neg_zero, d.fr_zero, div_eq_iff (Units.ne_zero _)] at hc
  ext
  simpa using hc

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumEigenInertPlaceLatticeStabiliser
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VDblEig

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem star_mem_SB' {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => star (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (star_zero _)⟩

theorem vdbl_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv d' hd' dd omd hdc hsp r hr g hg
  obtain ⟨hvSB, -, θ, hθ, hvac⟩ := hT.geo.hM.vac v
  set φ := G.M.vac v with hφ
  set vD := boxFun φ (fun x => star (φ x)) with hvD
  set RD := boxFun r (fun x => star (r x)) with hRD
  have hvDSB : vD ∈ SB _ := boxFun_mem_SB' hvSB (star_mem_SB' hvSB)
  have hS : boxFun (tens (evFin F v) φ r) (fun x => star (tens (evFin F v) φ r x)) = tens (evFin F v) vD RD := by
    funext x
    simp only [tens, boxFun, hvD, hRD, Function.comp_def, star_mul']
    ring
  have hRest : Rest (evFin F v) vD RD := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      show r ((x + z) ∘ Sum.inl) * star (r ((x + z) ∘ Sum.inr)) = r (x ∘ Sum.inl) * star (r (x ∘ Sum.inr))
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hr.1 _ _ hz1, hr.1 _ _ hz2]
    · rw [← hS]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hr.2 _ (GlobalTheory.ConjSch.star_mem_schA _ _ hr.2)

  have hU := hsp.2.1
  obtain ⟨φ₁, hφ₁, hA⟩ : ∃ φ₁ ∈ SB _, Acts (evFin F v) (omd g) vD φ₁ := by
    refine GlobalTheory.DblActs.acts_of_comm v B.ψ hT.base.std (omd g) (fun Φ hΦ => hU.pres g Φ hΦ)
      (fun μ hμ Φ hΦ => hU.unit μ hμ g Φ hΦ) ?_ vD hvDSB
    intro u hu x y Φ hΦ
    set z := dd.e.symm (x, y) with hz
    have he : dd.e (u • z) = (u • x, u • y) := by
      rw [LinearEquiv.map_smul, hz, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h2 := hg.1 u hu
    have e2 : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) g (u • z) = u • z := by
      simp only [actB]
      set P := GlobalTheory.DblVac.matD g with hP
      set c : AE F E := algebraMap (AF F) (AE F E) u with hc
      have hs1 : u • z = c • z := (algebraMap_smul (AE F E) u z).symm
      have hs2 : u • (P - 1) = c • (P - 1) := (algebraMap_smul (AE F E) u (P - 1)).symm
      have h2' : c • (P - 1) = 0 := hs2 ▸ h2
      have : (c • z) * Pᵀ - c • z = z * (c • (P - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2'] at this
      simp only [Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      rw [hs1]
      exact this
    have h3 := hU.impl g (u • z) Φ hΦ
    simp only [Darboux.rho] at h3
    set_option backward.isDefEq.respectTransparency false in
      rw [e2, he] at h3
    exact h3
  have hE0 := GlobalTheory.T.doubledVacuum_heisenbergEigen_doubledLattice F E σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac
  have hE1 := GlobalTheory.T.doubledStabilizer_weilOperator_transports_latticeEigen F E σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac omd hsp g hg vD hvDSB φ₁ hφ₁ hE0 hA
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.inertPlace_doubledEigenfunctions_line_vacuum F E σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac φ₁ hφ₁ hE1
  refine ⟨μ, ?_⟩
  rw [hS, hA RD hRest, hμ]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.VDblEig

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombination
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLin

theorem sp_dual_subsingleton (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem sE_comb : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  intro V _ _ D F _ _ k β s n a σF hs r J hJ hr
  have hW : ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L (DegPre.famφ D F β)
      (fun k' => J (redE F ≫ r ≫ DegPre.famφ D F β k')) := by
    intro y _
    haveI := sp_dual_subsingleton F
    let z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
    have hy : y = (redE F).base z := Subsingleton.elim _ _
    refine Set.mem_iInter.2 fun k' => ?_
    have := hJ (redE F ≫ r ≫ DegPre.famφ D F β k') (Set.mem_univ z)
    subst hy
    simpa using this
  unfold sE
  refine (congrArg (valR r _) (hs _)).trans ((GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).trans ((map_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans ?_)))
  congr 1
  · refine (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm.trans ?_
    rw [← TrivSqZeroExt.algebraMap_eq_inl]
    exact GlobalTheory.ZH.FormCount.valR_scal (algebraMap F (DualNumber F)) r _ hr _ hW (a i)
  · exact (GlobalTheory.ZH.CrdCalc.valR_eq r _ hW _).symm

end GlobalTheory.DualLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigFrameMatch
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.EigParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Generic

variable {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (x : Sp R ⟶ S) (χ : 𝓞 E → R)

def IsBasG {n : ℕ} (u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ (∀ i (a : 𝓞 E), u i ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ u i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x u a w

end Generic

variable {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S}

theorem comb_iff {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) (a : Fin n → R) (w : epsAt x ⟶ t.G) :
    IsCombAt x a v w ↔ IsCombAtG t x (fun i => (v i).left) a w.left :=
  exists_congr fun _ => and_congr Iff.rfl ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h.symm⟩

theorem basis_iff (χ : 𝓞 E →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) :
    IsEigBasisAt t.act x χ v ↔ IsBasG t x χ (fun i => (v i).left) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨Over.w (v i), (h1 i).1⟩, fun i a => (h1 i).2 a, fun w hw he => ?_⟩
    let w' : epsAt x ⟶ t.G := Over.homMk w hw.1
    exact (existsUnique_congr fun a => comb_iff v a w').1 (h2 w' ⟨hw.2, he⟩)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ⟨(h1 i).2, h2 i⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => comb_iff v a w).2 (h3 w.left ⟨Over.w w, hw.1⟩ hw.2)

theorem exists_over (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hu : IsBasG t x χ u) :
    ∃ v : Fin n → (epsAt x ⟶ t.G), IsEigBasisAt t.act x χ v ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => Over.homMk (u i) (hu.1 i).1, (basis_iff χ _).2 hu, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem exists_left (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) :
    ∃ u : Fin m → (Sp (DualNumber R) ⟶ t.G.left), IsBasG t x χ u ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => (v i).left, (basis_iff χ _).1 hv, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem eigFrame_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∀ (V : Set (gen Y)) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y), x ≫ genStr Y = spMap j → Set.range x ⊆ V → ∀ f : EigFrame Y j (x ≫ genι Y), (∃ v w, FrY Y V τ j x v w ∧ Match τ f v w) ∧ ∀ v w, FrY Y V τ j x v w → ∃ f' : EigFrame Y j (x ≫ genι Y), Match τ f' v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ hτ V R _ j x hx hV f
  have hp : D.mult τ = D.p := GlobalTheory.Harm.mult_of_mem D hτ
  have hq : D.mult (conjEmb τ) = D.q := GlobalTheory.Harm.mult_conjEmb_of_mem D hτ
  have hne : conjEmb τ ≠ τ := fun e => (GlobalTheory.Harm.not_mem_hostType_iff H τ).2 (by rw [e]; exact hτ) hτ
  have hf : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (f.v σ) :=
    fun σ => ⟨f.tan σ, f.eig σ, f.basis σ⟩
  refine ⟨?_, fun v w h => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := exists_over _ hp (hf τ)
    obtain ⟨w, hw, hw'⟩ := exists_over _ hq (hf (conjEmb τ))
    refine ⟨v, w, ⟨hx, hV, hv, ?_⟩, hv', hw'⟩
    rw [comp_chi_bar]
    exact hw
  · obtain ⟨-, -, hv, hw⟩ := h
    rw [comp_chi] at hv
    rw [comp_chi_bar] at hw
    obtain ⟨v₁, a, a'⟩ := exists_left _ hp hv
    obtain ⟨w₁, b, b'⟩ := exists_left _ hq hw
    classical
    let g := Function.update (Function.update f.v τ v₁) (conjEmb τ) w₁
    have g1 : g τ = v₁ := by
      simp only [g, Function.update_of_ne hne.symm, Function.update_self]
    have g2 : g (conjEmb τ) = w₁ := Function.update_self _ _ _
    have hg : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (g σ) := fun σ => by
      by_cases e2 : σ = conjEmb τ
      · rw [e2, g2]; exact b
      by_cases e1 : σ = τ
      · rw [e1, g1]; exact a
      have : g σ = f.v σ := by simp only [g, Function.update_of_ne e2, Function.update_of_ne e1]
      rw [this]; exact hf σ
    refine ⟨⟨g, fun σ => (hg σ).1, fun σ => (hg σ).2.1, fun σ => (hg σ).2.2⟩, fun i k e => ?_, fun i k e => ?_⟩
    · exact (a' i k e).trans (congrFun g1 k).symm
    · exact (b' i k e).trans (congrFun g2 k).symm

end GlobalTheory.DetLine.EigParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}

theorem uvec_cv (b : A.B) (w : Pm Dw.mult) (z : Let Dw.mult) (r : Fin (A.N + 1)) :
    uvec (A.cv b) w z r = ((A.A b).map (cC A b) * uC A b w z.1) r z.2 := by
  obtain ⟨τ, j⟩ := z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [uvec, cellVec, Atlas.cv, uC, cellMat, cC, Matrix.mul_apply, Matrix.map_apply, Matrix.submatrix_apply,
    Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul, id,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
  ring

variable {Z : Scheme.{0}} {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]
  {S : Type} [CommRing S]

theorem eq_spMap_ev (k : A.B × Pm Dw.mult) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    spMap ((ev z _ hz).comp (cellθ κ k).toRingHom) ≫ κ k.1 k.2 = z := by
  rw [← spMap_comp', Category.assoc, spMap_cellθ, spMap_ev]

end GlobalTheory.FlagMod.FieldFlag
end
end

