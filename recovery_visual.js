const stage = new Stage()

// ==============================
// HELPERS
// ==============================

function getTuples(fieldName) {
  return instance.field(fieldName).tuples()
}

function getAtoms(sigName) {
  return instance.signature(sigName).atoms()
}

// Extract mapping: (a -> b)
function mapFromTuples(tuples, keyIndex, valIndex) {
  let map = {}
  for (let t of tuples) {
    const atoms = t.atoms()
    const key = atoms[keyIndex].id()
    const val = atoms[valIndex].id()
    map[key] = val
  }
  return map
}

function addText(text, x, y, fontSize, color) {
  stage.add(new TextBox({
    text: text,
    coords: { x: x, y: y },
    fontSize: fontSize,
    color: color || "black"
  }))
}

function addCell(text, x, y, width, color) {
  stage.add(new Rectangle({
    coords: { x: x, y: y },
    width: width,
    height: 36,
    color: color,
    borderColor: "#1f2937",
    borderWidth: 1,
    label: text,
    labelSize: 14
  }))
}

function cleanEnumName(name) {
  return name.replace(/^(Normal|Crashed|Analysis|Redo|Undo|Done|Active|Committed|Aborted)0$/, "$1")
}

const TOP = 105
const ROW_HEIGHT = 46
const TX_X = 80
const TX_W = 230
const MEM_X = 370
const MEM_W = 170
const DISK_X = 600
const DISK_W = 170
const LOG_X = 830
const LOG_W = 220
const HEADER_Y = 78
const TRANSACTION_COLOR = "#dbeafe"
const MEMORY_COLOR = "#dcfce7"
const DISK_COLOR = "#fef3c7"
const LOG_COLOR = "#fce7f3"

// ==============================
// SYSTEM PHASE
// ==============================

const systemAtom = getAtoms("System")[0]
const phaseTuple = getTuples("phase").find(t => t.atoms()[0].id() === systemAtom.id())
const currentPhase = cleanEnumName(phaseTuple.atoms()[1].id())

addText(`Phase: ${currentPhase}`, 180, 28, 20)

// ==============================
// TRANSACTIONS
// ==============================

const transactions = getAtoms("Transaction")
const tStateMap = mapFromTuples(getTuples("tState"), 0, 1)

addText("Transactions", TX_X + TX_W / 2, HEADER_Y, 16)

transactions.forEach((t, i) => {
  addCell(
    `${t.id()}: ${cleanEnumName(tStateMap[t.id()])}`,
    TX_X,
    TOP + i * ROW_HEIGHT,
    TX_W,
    TRANSACTION_COLOR
  )
})

// ==============================
// MEMORY (BUFFER POOL)
// ==============================

const memMap = mapFromTuples(getTuples("memPages"), 0, 1)

addText("Memory", MEM_X + MEM_W / 2, HEADER_Y, 16)

Object.keys(memMap).forEach((page, i) => {
  addCell(`${page}: ${memMap[page]}`, MEM_X, TOP + i * ROW_HEIGHT, MEM_W, MEMORY_COLOR)
})

// ==============================
// DISK
// ==============================

const diskMap = mapFromTuples(getTuples("diskPages"), 0, 1)

addText("Disk", DISK_X + DISK_W / 2, HEADER_Y, 16)

Object.keys(diskMap).forEach((page, i) => {
  addCell(`${page}: ${diskMap[page]}`, DISK_X, TOP + i * ROW_HEIGHT, DISK_W, DISK_COLOR)
})

// ==============================
// LOG RECORDS (WAL)
// ==============================

const logTuples = getTuples("records")

let logs = []

for (let t of logTuples) {
  const atoms = t.atoms()
  const lsn = parseInt(atoms[1].id())
  const record = atoms[2]
  logs.push({ lsn, record })
}

// sort by LSN
logs.sort((a, b) => a.lsn - b.lsn)

addText("Log (WAL)", LOG_X + LOG_W / 2, HEADER_Y, 16)

logs.forEach((entry, i) => {
  addCell(`${entry.lsn}: ${entry.record.id()}`, LOG_X, TOP + i * ROW_HEIGHT, LOG_W, LOG_COLOR)
})

// ==============================
// FLUSHED LSN MARKER
// ==============================

const flushedTuples = getTuples("flushedLSN")
const flushedValue = flushedTuples.length > 0
  ? flushedTuples[0].atoms()[1].id()
  : "None"

addText(`Flushed LSN: ${flushedValue}`, LOG_X + LOG_W / 2, 38, 14)

// ==============================
// RENDER
// ==============================

stage.render(svg, document)
