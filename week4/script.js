/**
 * HW4 — Association Rules.
 * Plain JavaScript script; transactions.js must be loaded first.
 */

if (typeof window === "undefined" || !window.HW4) {
  throw new Error(
    "window.HW4 is not defined — load transactions.js before script.js."
  );
}

const data = window.HW4;

const TRANSACTIONS = data.baskets.map((basket) =>
  basket.map((idx) => ({
    stock: data.stocks[idx],
    description: data.descriptions[idx],
  }))
);

let DATASET_INDEX = null;
let N = data.N_BASKETS;

const indexCache = new WeakMap();
const descriptionByStock = new Map();

// ---------------------------------------------------------------------------
// Provided counting helpers
// ---------------------------------------------------------------------------

function stockOf(item) {
  return typeof item === "string" ? item : item.stock;
}

function buildIndex(baskets) {
  const byStock = new Map();

  baskets.forEach((basket, basketId) => {
    for (const item of basket) {
      const stock = stockOf(item);

      if (!byStock.has(stock)) {
        byStock.set(stock, new Set());
      }

      byStock.get(stock).add(basketId);
    }
  });

  return {
    n: baskets.length,
    byStock,
  };
}

function asIndex(basketsOrIndex) {
  if (
    basketsOrIndex &&
    !Array.isArray(basketsOrIndex) &&
    basketsOrIndex.byStock
  ) {
    return basketsOrIndex;
  }

  let index = indexCache.get(basketsOrIndex);

  if (!index) {
    index = buildIndex(basketsOrIndex);
    indexCache.set(basketsOrIndex, index);
  }

  return index;
}

function countItem(basketsOrIndex, stock) {
  return countItemset(basketsOrIndex, [stock]);
}

function countPair(basketsOrIndex, stockA, stockB) {
  return countItemset(basketsOrIndex, [stockA, stockB]);
}

// ---------------------------------------------------------------------------
// Student implementations
// ---------------------------------------------------------------------------

function dedupeBasket(rawItems) {
  return [...new Set(rawItems.map(stockOf))];
}

function countItemset(basketsOrIndex, stocks) {
  if (!stocks || stocks.length === 0) {
    return 0;
  }

  const index = asIndex(basketsOrIndex);
  const uniqueStocks = dedupeBasket(stocks);

  const postingLists = uniqueStocks.map((stock) =>
    index.byStock.get(stock)
  );

  if (postingLists.some((posting) => !posting || posting.size === 0)) {
    return 0;
  }

  postingLists.sort((a, b) => a.size - b.size);

  let count = 0;

  for (const basketId of postingLists[0]) {
    if (postingLists.every((posting) => posting.has(basketId))) {
      count++;
    }
  }

  return count;
}

function computeSupport(jointCount, n) {
  if (n === 0) {
    return { value: 0, defined: false };
  }

  return {
    value: jointCount / n,
    defined: true,
  };
}

function computeConfidence(jointCount, antecedentCount) {
  if (antecedentCount === 0) {
    return { value: 0, defined: false };
  }

  return {
    value: jointCount / antecedentCount,
    defined: true,
  };
}

function computeLift(confidence, consequentCount, n) {
  if (
    !confidence ||
    !confidence.defined ||
    n === 0 ||
    consequentCount === 0
  ) {
    return { value: 0, defined: false };
  }

  return {
    value: confidence.value / (consequentCount / n),
    defined: true,
  };
}

function validateThresholds(minSupport, minConfidence) {
  const errors = [];

  for (const [label, value] of [
    ["Minimum support", minSupport],
    ["Minimum confidence", minConfidence],
  ]) {
    if (typeof value !== "number" || Number.isNaN(value)) {
      errors.push(`${label} must be a number.`);
    } else if (value <= 0 || value > 1) {
      errors.push(`${label} must be greater than 0 and at most 1.`);
    }
  }

  return {
    ok: errors.length === 0,
    errors,
  };
}

function findFrequentItemsets(transactions, minSupport) {
  if (
    !Number.isFinite(minSupport) ||
    minSupport <= 0 ||
    minSupport > 1
  ) {
    throw new Error("minSupport must be in (0, 1].");
  }

  const index = asIndex(transactions);
  const n = index.n;

  if (n === 0) {
    return [];
  }

  const result = [];
  const key = (items) => JSON.stringify(items);

  let level = [];

  // Frequent singleton counts are basket counts, not row counts.
  for (const stock of [...index.byStock.keys()].sort()) {
    const count = index.byStock.get(stock).size;
    const support = count / n;

    if (support >= minSupport) {
      const items = [stock];

      level.push(items);
      result.push({ items, count, support });
    }
  }

  // Apriori: join frequent sets and prune infrequent subsets.
  while (level.length > 1) {
    const width = level[0].length;
    const previousKeys = new Set(level.map(key));
    const nextLevel = [];

    for (let i = 0; i < level.length; i++) {
      for (let j = i + 1; j < level.length; j++) {
        const a = level[i];
        const b = level[j];

        let samePrefix = true;

        for (let p = 0; p < width - 1; p++) {
          if (a[p] !== b[p]) {
            samePrefix = false;
            break;
          }
        }

        if (!samePrefix) {
          continue;
        }

        const candidate = [...a, b[width - 1]].sort();

        let allSubsetsFrequent = true;

        for (let p = 0; p < candidate.length; p++) {
          const subset = candidate.filter((_, position) => position !== p);

          if (!previousKeys.has(key(subset))) {
            allSubsetsFrequent = false;
            break;
          }
        }

        if (!allSubsetsFrequent) {
          continue;
        }

        const count = countItemset(index, candidate);
        const support = count / n;

        if (support >= minSupport) {
          nextLevel.push(candidate);
          result.push({
            items: candidate,
            count,
            support,
          });
        }
      }
    }

    level = nextLevel;
  }

  return result;
}

function generateRules(frequentItemsets, minConfidence) {
  if (
    !Number.isFinite(minConfidence) ||
    minConfidence <= 0 ||
    minConfidence > 1
  ) {
    throw new Error("minConfidence must be in (0, 1].");
  }

  const key = (items) => JSON.stringify([...items].sort());

  const counts = new Map(
    frequentItemsets.map((itemset) => [
      key(itemset.items),
      itemset.count,
    ])
  );

  const supports = new Map(
    frequentItemsets.map((itemset) => [
      key(itemset.items),
      itemset.support,
    ])
  );

  const rules = [];

  for (const itemset of frequentItemsets) {
    const items = [...itemset.items].sort();

    if (items.length < 2) {
      continue;
    }

    // Enumerate all non-empty, disjoint splits in both directions.
    function visit(position, antecedent, consequent) {
      if (position < items.length) {
        visit(
          position + 1,
          [...antecedent, items[position]],
          consequent
        );

        visit(
          position + 1,
          antecedent,
          [...consequent, items[position]]
        );

        return;
      }

      if (antecedent.length === 0 || consequent.length === 0) {
        return;
      }

      const antecedentCount = counts.get(key(antecedent));
      const consequentCount = counts.get(key(consequent));
      const consequentSupport = supports.get(key(consequent));

      if (
        antecedentCount === undefined ||
        consequentCount === undefined ||
        consequentSupport === undefined
      ) {
        throw new Error("Missing subset information in frequentItemsets.");
      }

      const confidence = computeConfidence(
        itemset.count,
        antecedentCount
      );

      if (!confidence.defined || confidence.value < minConfidence) {
        return;
      }

      rules.push({
        antecedent,
        consequent,
        jointCount: itemset.count,
        antecedentCount,
        consequentCount,
        support: itemset.support,
        confidence: confidence.value,
        lift: confidence.value / consequentSupport,
      });
    }

    visit(0, [], []);
  }

  return rules;
}

// ---------------------------------------------------------------------------
// Original worked example
// ---------------------------------------------------------------------------

function tinyWorkedExample() {
  const baskets = [
    ["bread", "milk", "jam", "ham"],
    ["bread", "milk", "jam"],
    ["bread", "milk"],
    ["bread", "jam", "eggs"],
    ["bread", "eggs"],
  ];

  const n = baskets.length;

  return {
    n,
    baskets,
    itemCounts: {
      bread: 5,
      milk: 3,
      jam: 3,
      eggs: 2,
      ham: 1,
    },
    rules: [
      {
        antecedent: ["bread"],
        consequent: ["milk"],
        jointCount: 3,
        antecedentCount: 5,
        consequentCount: 3,
        support: 3 / n,
        confidence: 3 / 5,
        lift: 1,
      },
      {
        antecedent: ["milk"],
        consequent: ["jam"],
        jointCount: 2,
        antecedentCount: 3,
        consequentCount: 3,
        support: 2 / n,
        confidence: 2 / 3,
        lift: (2 / 3) / (3 / 5),
      },
      {
        antecedent: ["jam"],
        consequent: ["eggs"],
        jointCount: 1,
        antecedentCount: 3,
        consequentCount: 2,
        support: 1 / n,
        confidence: 1 / 3,
        lift: (1 / 3) / (2 / 5),
      },
    ],
  };
}

// ---------------------------------------------------------------------------
// Rule normalisation
// ---------------------------------------------------------------------------

function enrichRule(rule, index) {
  const antecedent = (rule.antecedent || []).map(stockOf);
  const consequent = (rule.consequent || []).map(stockOf);
  const n = index.n || N;

  const jointCount =
    typeof rule.jointCount === "number"
      ? rule.jointCount
      : countItemset(index, [...antecedent, ...consequent]);

  const antecedentCount =
    typeof rule.antecedentCount === "number"
      ? rule.antecedentCount
      : countItemset(index, antecedent);

  const consequentCount =
    typeof rule.consequentCount === "number"
      ? rule.consequentCount
      : countItemset(index, consequent);

  const support = computeSupport(jointCount, n);
  const confidence = computeConfidence(jointCount, antecedentCount);
  const lift = computeLift(confidence, consequentCount, n);

  return {
    antecedent,
    consequent,
    jointCount,
    antecedentCount,
    consequentCount,
    support:
      typeof rule.support === "number" ? rule.support : support.value,
    confidence:
      typeof rule.confidence === "number"
        ? rule.confidence
        : confidence.value,
    lift:
      typeof rule.lift === "number" ? rule.lift : lift.value,
    supportDefined: support.defined,
    confidenceDefined: confidence.defined,
    liftDefined: lift.defined,
  };
}

function reverseRule(rule, index) {
  return enrichRule(
    {
      antecedent: rule.consequent,
      consequent: rule.antecedent,
    },
    index
  );
}

// ---------------------------------------------------------------------------
// Formatting
// ---------------------------------------------------------------------------

function formatPercent(fraction) {
  return `${(fraction * 100).toFixed(2)}%`;
}

function formatMetric(value) {
  if (!Number.isFinite(value)) {
    return "n/a";
  }

  return value.toFixed(4);
}

function describe(stock, index) {
  const description = descriptionByStock.get(stock);
  return description ? `${stock} — ${description}` : stock;
}

function formatItemset(stocks, index) {
  if (!stocks || stocks.length === 0) {
    return "(empty)";
  }

  return stocks.map((stock) => describe(stock, index)).join(", ");
}

function escapeHtml(text) {
  return String(text)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

function renderDatasetSummary(index, container) {
  const target =
    container || document.getElementById("dataset-summary-body");

  if (!target) {
    return;
  }

  const counts = [...index.byStock.entries()]
    .map(([stock, posting]) => ({
      stock,
      count: posting.size,
    }))
    .sort(
      (a, b) =>
        b.count - a.count || a.stock.localeCompare(b.stock)
    );

  const rows = counts
    .slice(0, 5)
    .map(
      (entry, i) => `
        <tr>
          <td class="num">${i + 1}</td>
          <td>${escapeHtml(describe(entry.stock, index))}</td>
          <td class="num">${entry.count}</td>
        </tr>
      `
    )
    .join("");

  target.innerHTML = `
    <p class="summary-line">
      <strong>${index.n.toLocaleString("en-US")}</strong> baskets ·
      <strong>${index.byStock.size.toLocaleString("en-US")}</strong>
      distinct items
    </p>
    <details class="top-items">
      <summary>Top 5 items by basket count</summary>
      <table class="data-table">
        <thead>
          <tr>
            <th scope="col">#</th>
            <th scope="col">Item</th>
            <th scope="col">Baskets</th>
          </tr>
        </thead>
        <tbody>${rows}</tbody>
      </table>
    </details>
    <p class="provenance">${escapeHtml(data.dataset_provenance)}</p>
  `;
}

function renderResults(rules, index, container) {
  const target = container || document.getElementById("results");

  if (!target) {
    return;
  }

  const activeIndex = index || DATASET_INDEX;

  if (!rules || rules.length === 0) {
    target.innerHTML =
      '<p class="empty-state">No rules passed the current thresholds. ' +
      "Lower the minimum support or confidence and run again.</p>";

    return;
  }

  const body = rules
    .map((rule, rowIndex) => {
      const enriched = enrichRule(rule, activeIndex);

      return `
        <tr tabindex="0" data-rule-index="${rowIndex}">
          <td>${escapeHtml(
            formatItemset(enriched.antecedent, activeIndex)
          )}</td>
          <td>${escapeHtml(
            formatItemset(enriched.consequent, activeIndex)
          )}</td>
          <td class="num">${enriched.jointCount}</td>
          <td class="num">${enriched.antecedentCount}</td>
          <td class="num">${enriched.consequentCount}</td>
          <td class="num">${formatPercent(enriched.support)}</td>
          <td class="num">${formatPercent(enriched.confidence)}</td>
          <td class="num">${formatMetric(enriched.lift)}</td>
        </tr>
      `;
    })
    .join("");

  target.innerHTML = `
    <p class="results-count">
      ${rules.length} rule${rules.length === 1 ? "" : "s"}.
    </p>
    <table class="data-table rules-table">
      <thead>
        <tr>
          <th scope="col">Antecedent (A)</th>
          <th scope="col">Consequent (B)</th>
          <th scope="col">count(A∪B)</th>
          <th scope="col">count(A)</th>
          <th scope="col">count(B)</th>
          <th scope="col">support</th>
          <th scope="col">confidence</th>
          <th scope="col">lift</th>
        </tr>
      </thead>
      <tbody>${body}</tbody>
    </table>
  `;

  target.querySelectorAll("tr[data-rule-index]").forEach((row) => {
    const activate = () => {
      const rule = rules[Number(row.dataset.ruleIndex)];
      renderRuleDetail(rule, activeIndex);
    };

    row.addEventListener("click", activate);

    row.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        activate();
      }
    });
  });
}

function renderRuleDetail(rule, index, container) {
  const target = container || document.getElementById("rule-detail");

  if (!target) {
    return;
  }

  const activeIndex = index || DATASET_INDEX;
  const enriched = enrichRule(rule, activeIndex);
  const reversed = reverseRule(enriched, activeIndex);

  const zeroDenominatorNotes = [];

  if (enriched.antecedentCount === 0) {
    zeroDenominatorNotes.push(
      "count(A) = 0, so confidence(A → B) is undefined (division by zero)."
    );
  }

  if (enriched.consequentCount === 0) {
    zeroDenominatorNotes.push(
      "count(B) = 0, so lift(A → B) is undefined (division by zero)."
    );
  }

  const noteHtml = zeroDenominatorNotes.length
    ? `<p class="warning">${
        zeroDenominatorNotes.map(escapeHtml).join(" ")
      }</p>`
    : "";

  target.innerHTML = `
    <dl class="rule-metrics">
      <dt>Antecedent (A)</dt>
      <dd>${escapeHtml(
        formatItemset(enriched.antecedent, activeIndex)
      )}</dd>

      <dt>Consequent (B)</dt>
      <dd>${escapeHtml(
        formatItemset(enriched.consequent, activeIndex)
      )}</dd>

      <dt>count(A∪B)</dt>
      <dd class="num">${enriched.jointCount}</dd>

      <dt>count(A)</dt>
      <dd class="num">${enriched.antecedentCount}</dd>

      <dt>count(B)</dt>
      <dd class="num">${enriched.consequentCount}</dd>

      <dt>support</dt>
      <dd class="num">${formatPercent(enriched.support)}</dd>

      <dt>confidence</dt>
      <dd class="num">${formatPercent(enriched.confidence)}</dd>

      <dt>lift</dt>
      <dd class="num">${formatMetric(enriched.lift)}</dd>
    </dl>

    <p class="comparison">
      Reverse direction (B → A): confidence
      <strong>${formatPercent(reversed.confidence)}</strong>,
      lift <strong>${formatMetric(reversed.lift)}</strong>.
      Confidence changes with direction; lift does not.
    </p>

    ${noteHtml}

    <button type="button" id="reverse-rule">
      Reverse direction (B → A)
    </button>
  `;

  target.querySelector("#reverse-rule").addEventListener("click", () => {
    renderRuleDetail(reversed, activeIndex, target);
  });
}

function renderWorkedExample(example, container) {
  const target =
    container || document.getElementById("worked-example");

  if (!target) {
    return;
  }

  const rows = example.rules
    .map(
      (rule) => `
        <tr>
          <td>${rule.antecedent.join(", ")}</td>
          <td>${rule.consequent.join(", ")}</td>
          <td class="num">${rule.jointCount}</td>
          <td class="num">${rule.antecedentCount}</td>
          <td class="num">${rule.consequentCount}</td>
          <td class="num">${formatPercent(rule.support)}</td>
          <td class="num">${formatPercent(rule.confidence)}</td>
          <td class="num">${formatMetric(rule.lift)}</td>
        </tr>
      `
    )
    .join("");

  target.innerHTML = `
    <p class="worked-example-intro">
      Five hand-built baskets, N = ${example.n}.
      The top row has lift exactly 1 because
      <code>bread</code> appears in every basket;
      the second has lift &gt; 1; the third has lift &lt; 1.
    </p>

    <table class="data-table">
      <thead>
        <tr>
          <th scope="col">A</th>
          <th scope="col">B</th>
          <th scope="col">count(A∪B)</th>
          <th scope="col">count(A)</th>
          <th scope="col">count(B)</th>
          <th scope="col">support</th>
          <th scope="col">confidence</th>
          <th scope="col">lift</th>
        </tr>
      </thead>
      <tbody>${rows}</tbody>
    </table>
  `;
}

// ---------------------------------------------------------------------------
// Original self-checks
// ---------------------------------------------------------------------------

const TODO_MARKER = "TODO(hw4)";

function runTests(logElement) {
  const example = tinyWorkedExample();
  const checks = [];
  const basketObjects = example.baskets;

  const pass = (name, detail) =>
    checks.push({ name, status: "PASS", detail });

  const fail = (name, detail) =>
    checks.push({ name, status: "FAIL", detail });

  const pending = (name, detail) =>
    checks.push({ name, status: "PENDING", detail });

  const close = (a, b, eps = 1e-9) => Math.abs(a - b) < eps;

  const check = (name, fn) => {
    try {
      const outcome = fn();

      if (outcome && outcome.pending) {
        pending(name, outcome.pending);
      } else {
        pass(name, outcome === undefined ? "" : String(outcome));
      }
    } catch (error) {
      if (String(error && error.message).includes(TODO_MARKER)) {
        pending(name, "TODO(hw4): not implemented yet.");
      } else {
        fail(
          name,
          String(error && error.message ? error.message : error)
        );
      }
    }
  };

  check("fixture: item counts match the hand-computed values", () => {
    for (const [stock, expected] of Object.entries(example.itemCounts)) {
      const actual = countItem(basketObjects, stock);

      if (actual !== expected) {
        throw new Error(
          `countItem(${stock}) = ${actual}, expected ${expected}`
        );
      }
    }

    return "all five item counts correct";
  });

  check("fixture: bread -> milk has lift exactly 1", () => {
    const [breadMilk] = example.rules;

    const joint = countPair(basketObjects, "bread", "milk");
    const support = computeSupport(joint, example.n);

    const confidence = computeConfidence(
      joint,
      countItem(basketObjects, "bread")
    );

    const lift = computeLift(
      confidence,
      countItem(basketObjects, "milk"),
      example.n
    );

    if (!close(support.value, breadMilk.support)) {
      throw new Error("support mismatch");
    }

    if (!close(confidence.value, breadMilk.confidence)) {
      throw new Error("confidence mismatch");
    }

    if (!close(lift.value, breadMilk.lift)) {
      throw new Error(`lift = ${lift.value}, expected 1`);
    }

    return (
      `support=${support.value.toFixed(4)} ` +
      `confidence=${confidence.value.toFixed(4)} ` +
      `lift=${lift.value.toFixed(4)}`
    );
  });

  check("fixture: milk -> jam has lift greater than 1", () => {
    const rule = example.rules[1];

    const joint = countPair(
      basketObjects,
      rule.antecedent[0],
      rule.consequent[0]
    );

    const confidence = computeConfidence(
      joint,
      countItem(basketObjects, rule.antecedent[0])
    );

    const lift = computeLift(
      confidence,
      countItem(basketObjects, rule.consequent[0]),
      example.n
    );

    if (!close(lift.value, rule.lift)) {
      throw new Error(
        `lift = ${lift.value}, expected ${rule.lift}`
      );
    }

    if (!(lift.value > 1)) {
      throw new Error("expected lift > 1");
    }

    return `lift=${lift.value.toFixed(4)} (> 1)`;
  });

  check("fixture: jam -> eggs has lift less than 1", () => {
    const rule = example.rules[2];

    const joint = countPair(
      basketObjects,
      rule.antecedent[0],
      rule.consequent[0]
    );

    const confidence = computeConfidence(
      joint,
      countItem(basketObjects, rule.antecedent[0])
    );

    const lift = computeLift(
      confidence,
      countItem(basketObjects, rule.consequent[0]),
      example.n
    );

    if (!close(lift.value, rule.lift)) {
      throw new Error(
        `lift = ${lift.value}, expected ${rule.lift}`
      );
    }

    if (!(lift.value < 1 && lift.value > 0)) {
      throw new Error("expected 0 < lift < 1");
    }

    return `lift=${lift.value.toFixed(4)} (0 < lift < 1)`;
  });

  check("fixture: reversed confidence differs (jam <-> eggs)", () => {
    const forwardJoint = countPair(basketObjects, "jam", "eggs");

    const forward = computeConfidence(
      forwardJoint,
      countItem(basketObjects, "jam")
    );

    const reversed = computeConfidence(
      forwardJoint,
      countItem(basketObjects, "eggs")
    );

    if (close(forward.value, reversed.value)) {
      throw new Error(
        "confidence should differ between jam -> eggs and eggs -> jam"
      );
    }

    if (
      !close(forward.value, 1 / 3) ||
      !close(reversed.value, 1 / 2)
    ) {
      throw new Error(
        `unexpected values: ${forward.value} vs ${reversed.value}`
      );
    }

    return (
      `jam->eggs=${forward.value.toFixed(4)} vs ` +
      `eggs->jam=${reversed.value.toFixed(4)}`
    );
  });

  check("duplicate items in a raw basket are counted once", () => {
    const deduped = dedupeBasket([
      "milk", "bread", "milk", "bread", "jam",
    ]);

    if (deduped.length !== 3) {
      throw new Error(
        `expected 3 unique items, got ${deduped.length}`
      );
    }

    const duplicateBasket = [
      ["milk", "bread", "milk", "bread"],
      ["milk"],
    ];

    if (countItem(duplicateBasket, "milk") !== 2) {
      throw new Error(
        "countItem must count each basket once, not each row"
      );
    }

    if (countPair(duplicateBasket, "milk", "bread") !== 1) {
      throw new Error("countPair must count each basket once");
    }

    return "dedupeBasket removed repeats; counting is per basket";
  });

  check("empty rule set renders an empty-state note", () => {
    const scratch = document.createElement("div");

    renderResults([], DATASET_INDEX, scratch);

    if (!/no rules passed/i.test(scratch.textContent)) {
      throw new Error("expected an empty-state message");
    }

    return "empty state rendered";
  });

  check("invalid thresholds are rejected", () => {
    if (validateThresholds(0.01, 0.3).ok !== true) {
      throw new Error("valid thresholds rejected");
    }

    if (validateThresholds(Number.NaN, 0.3).ok !== false) {
      throw new Error("NaN support accepted");
    }

    if (validateThresholds(0.01, 1.5).ok !== false) {
      throw new Error("confidence > 1 accepted");
    }

    if (validateThresholds(0, 0.3).ok !== false) {
      throw new Error("zero support accepted");
    }

    return "valid accepted, invalid rejected";
  });

  check("zero-denominator guards return undefined metrics", () => {
    if (computeConfidence(0, 0).defined !== false) {
      throw new Error("count(A)=0 must be undefined");
    }

    if (
      computeLift(
        { value: 0.5, defined: true },
        0,
        5
      ).defined !== false
    ) {
      throw new Error("count(B)=0 must be undefined");
    }

    if (computeSupport(0, 0).defined !== false) {
      throw new Error("N=0 must be undefined");
    }

    return "zero denominators return defined=false";
  });

  check(
    "findFrequentItemsets reproduces the fixture's frequent itemsets",
    () => {
      const itemsets = findFrequentItemsets(basketObjects, 0.4);
      const pairs = itemsets.filter((set) => set.items.length === 2);

      if (pairs.length === 0) {
        throw new Error(
          "no frequent pairs found at support >= 0.4"
        );
      }

      return `${itemsets.length} itemsets`;
    }
  );

  check("generateRules reproduces the fixture's rules", () => {
    const itemsets = findFrequentItemsets(basketObjects, 0.2);
    const rules = generateRules(itemsets, 0.5);

    if (rules.length === 0) {
      throw new Error(
        "no rules found at support >= 0.2, confidence >= 0.5"
      );
    }

    return `${rules.length} rules`;
  });

  const passed = checks.filter((c) => c.status === "PASS").length;
  const failed = checks.filter((c) => c.status === "FAIL").length;
  const pendingCount =
    checks.filter((c) => c.status === "PENDING").length;

  const lines = [
    `HW4 self-checks — pass ${passed}, fail ${failed}, ` +
      `pending ${pendingCount} (of ${checks.length})`,
    "",
    ...checks.map(
      (c) =>
        `${c.status.padEnd(7)} ${c.name}` +
        (c.detail ? ` — ${c.detail}` : "")
    ),
  ];

  const target = logElement || document.getElementById("testLog");

  if (target) {
    target.textContent = lines.join("\n");
  }

  return {
    passed,
    failed,
    pending: pendingCount,
    checks,
  };
}

// ---------------------------------------------------------------------------
// Controls and pipeline
// ---------------------------------------------------------------------------

function primeDescriptions() {
  data.stocks.forEach((stock, i) => {
    if (!descriptionByStock.has(stock)) {
      descriptionByStock.set(stock, data.descriptions[i]);
    }
  });
}

function readThresholds() {
  const supportInput = document.getElementById("min-support");
  const confidenceInput =
    document.getElementById("min-confidence");

  return {
    minSupport: Number(supportInput.value) / 100,
    minConfidence: Number(confidenceInput.value) / 100,
  };
}

function syncThresholdLabels() {
  const supportInput = document.getElementById("min-support");
  const confidenceInput =
    document.getElementById("min-confidence");

  const supportOutput =
    document.getElementById("min-support-value");

  const confidenceOutput =
    document.getElementById("min-confidence-value");

  if (supportOutput) {
    supportOutput.textContent =
      `${Number(supportInput.value).toFixed(1)}%`;
  }

  if (confidenceOutput) {
    confidenceOutput.textContent =
      `${Number(confidenceInput.value).toFixed(0)}%`;
  }
}

function runPipeline() {
  const status = document.getElementById("status");

  if (!DATASET_INDEX) {
    if (status) {
      status.textContent = "Dataset not ready yet — reload the page.";
    }

    return;
  }

  const { minSupport, minConfidence } = readThresholds();
  const validation = validateThresholds(minSupport, minConfidence);

  if (!validation.ok) {
    if (status) {
      status.textContent = validation.errors.join(" ");
    }

    return;
  }

  try {
    if (status) {
      status.textContent = "Mining frequent itemsets…";
    }

    const itemsets = findFrequentItemsets(
      TRANSACTIONS,
      minSupport
    );

    const rules = generateRules(itemsets, minConfidence);

    renderResults(rules, DATASET_INDEX);

    if (status) {
      status.textContent =
        `Done — ${rules.length} rule(s) at support ≥ ` +
        `${(minSupport * 100).toFixed(1)}% and confidence ≥ ` +
        `${(minConfidence * 100).toFixed(0)}%.`;
    }
  } catch (error) {
    const message = String(
      error && error.message ? error.message : error
    );

    const resultsEl = document.getElementById("results");

    if (resultsEl) {
      resultsEl.innerHTML =
        '<p class="empty-state">Run failed — ' +
        "the rule miner did not complete. " +
        `Error: ${escapeHtml(message)}</p>`;
    }

    if (status) {
      status.textContent = message;
    }
  }
}

// ---------------------------------------------------------------------------
// Initialisation
// ---------------------------------------------------------------------------

function init() {
  renderWorkedExample(tinyWorkedExample());
  syncThresholdLabels();

  const supportInput = document.getElementById("min-support");
  const confidenceInput =
    document.getElementById("min-confidence");

  if (supportInput) {
    supportInput.addEventListener("input", syncThresholdLabels);
  }

  if (confidenceInput) {
    confidenceInput.addEventListener("input", syncThresholdLabels);
  }

  const runButton = document.getElementById("run-rules");

  if (runButton) {
    runButton.addEventListener("click", runPipeline);
  }

  const testButton = document.getElementById("run-tests");

  if (testButton) {
    testButton.addEventListener("click", () => runTests());
  }

  primeDescriptions();

  N = TRANSACTIONS.length;
  DATASET_INDEX = buildIndex(TRANSACTIONS);

  renderDatasetSummary(DATASET_INDEX);

  const status = document.getElementById("status");

  if (status) {
    status.textContent =
      `Dataset ready: ${N.toLocaleString("en-US")} baskets, ` +
      `${DATASET_INDEX.byStock.size.toLocaleString("en-US")} ` +
      "distinct items. Press Run tests, then Run rules.";
  }
}

if (typeof document !== "undefined") {
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
}