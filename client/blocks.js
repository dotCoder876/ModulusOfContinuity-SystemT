Blockly.Blocks['set_term'] = {
  init: function() {
    this.appendValueInput("NAME")
        .setCheck("Term")
        .appendField("term: ");
    this.setInputsInline(false);
    this.setColour(400);
    this.setDeletable(false);
 this.setTooltip("")
 this.setHelpUrl("");
  }
};

Blockly.Blocks['zero'] = {
  init: function() {
    this.appendDummyInput()
        .appendField("0");
    this.setInputsInline(true);
    this.setOutput(true, "Term");
    this.setColour(180);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};
Blockly.Blocks['variable'] = {
  init: function() {
    this.appendDummyInput()
        .appendField(new Blockly.FieldTextInput(""), "VAR");
    this.setInputsInline(true);
    this.setOutput(true, "Term");
    this.setColour(300);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};

Blockly.Blocks['abstraction'] = {
  init: function() {
    this.appendDummyInput()
        .appendField("λ")
        .appendField("(")
        .appendField(new Blockly.FieldTextInput(""), "ABVAR")
        .appendField(":");
    this.appendValueInput("ABTYPE")
        .setCheck("Type");
    this.appendDummyInput()
        .appendField(")")
        .appendField(".");
    this.appendValueInput("BODY")
        .setCheck("Term");
    this.appendDummyInput();
    this.setInputsInline(true);
    this.setOutput(true, "Term");
    this.setColour(340);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};

Blockly.Blocks['application'] = {
  init: function() {
    this.appendValueInput("LEFT")
        .setCheck("Term");
    this.appendValueInput("RIGHT")
        .setCheck("Term");
    this.setInputsInline(true);
    this.setOutput(true, "Term");
    this.setColour(200);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};

Blockly.Blocks['recursor'] = {
  init: function() {
    this.appendDummyInput()
        .appendField("rec");
    this.appendValueInput("RECTYPE")
        .setCheck("Type");
    this.setInputsInline(true);
    this.setOutput(true, "Term");
    this.setColour(260);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};
Blockly.Blocks['successor'] = {
  init: function() {
    this.appendDummyInput()
        .appendField("succ");
    this.setInputsInline(true);
    this.setOutput(true, "Term");
    this.setColour(220);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};

Blockly.Blocks['nat'] = {
  init: function() {
    this.appendDummyInput()
        .appendField("ℕ");
    this.setInputsInline(false);
    this.setOutput(true, "Type");
    this.setColour(20);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};

Blockly.Blocks['function'] = {
  init: function() {
    this.appendValueInput("DOM")
        .setCheck("Type");
    this.appendDummyInput()
        .appendField(new Blockly.FieldLabelSerializable("→"), "ARROW");
    this.appendValueInput("COD")
        .setCheck("Type");
    this.setInputsInline(true);
    this.setOutput(true, "Type");
    this.setColour(60);
 this.setTooltip("");
 this.setHelpUrl("");
  }
};

Blockly.Blocks['set_context'] = {
  init: function() {
    this.declarationCount_ = 3;
    this.updateShape_();
    this.setMutator(new Blockly.Mutator(['set_context_declaration']))
    this.setColour(450);
    this.setTooltip('set context');
  },
  mutationToDom: function() {
    var container = Blockly.utils.xml.createElement('mutation');
    container.setAttribute('declarations', this.declarationCount_);
    return container;
  },
  domToMutation: function(container) {
    this.declarationCount_ = parseInt(container.getAttribute('declarations'), 10);
    this.updateShape_();
  },
  decompose: function(workspace) {
    var containerBlock = workspace.newBlock('set_context_container');
    containerBlock.initSvg();
    var connection = containerBlock.getInput('STACK').connection;
    for (var i = 0; i < this.declarationCount_; i++) {
      var declarationBlock = workspace.newBlock('set_context_declaration');
      declarationBlock.initSvg();
      connection.connect(declarationBlock.previousConnection);
      connection = declarationBlock.nextConnection;
    }
    return containerBlock;
  },
  compose: function(containerBlock) {
    var declarationBlock = containerBlock.getInputTargetBlock('STACK');
    // Count number of inputs.
    var connections = [];
    var data = []
    while (declarationBlock && !declarationBlock.isInsertionMarker()) {
      connections.push(declarationBlock.valueConnection_);
      data.push(declarationBlock.userData_);
      declarationBlock = declarationBlock.nextConnection && 
          declarationBlock.nextConnection.targetBlock();
    }
    // Disconnect any children that don't belong.
    for (var i = 0; i < this.itemCount_; i++) {
      var connection = this.getInput('ADD' + i).connection.targetConnection;
      if (connection && connections.indexOf(connection) == -1) {
        connection.disconnect();
      }
    }
    for (var i = 0; i < this.optionCount_; i++) {
      this.setFieldValue(data[i] || 'option', 'USER' + i);
    }
    this.declarationCount_ = connections.length;
    this.updateShape_();
    // Reconnect any child blocks.
    for (var i = 0; i < this.itemCount_; i++) {
      Blockly.Mutator.reconnect(connections[i], this, 'ADD' + i);
    }
  },
  saveConnections: function(containerBlock) {
    // Store names and values for each option.
    var declarationBlock = containerBlock.getInputTargetBlock('STACK');
    var i = 0;
    while (declarationBlock) {
      var input = this.getInput('ADD' + i);
      declarationBlock.userData_ = this.getFieldValue('USER' + i);
      declarationBlock.valueConnection_ = input && input.connection.targetConnection;
      i++;
      declarationBlock = declarationBlock.nextConnection &&
        declarationBlock.nextConnection.targetBlock();
    }
  },
  updateShape_: function() {
    // if (this.declarationCount_ && this.getInput('EMPTY')) {
    //   this.removeInput('EMPTY');
    // } else if (!this.itemCount_ && !this.getInput('EMPTY')) {
    //   this.appendDummyInput('EMPTY')
    //       .appendField(Blockly.Msg['LISTS_CREATE_EMPTY_TITLE']);
    // }
    // Add new inputs.
    for (var i = 0; i < this.declarationCount_; i++) {
      if (!this.getInput('ADD' + i)) {
        var input = this.appendValueInput('ADD' + i).setCheck('Type')
            .appendField(new Blockly.FieldTextInput(''), 'USER' + i)
            .appendField(': ')
            .setAlign(Blockly.ALIGN_RIGHT);
        if (i == 0) {
          input.appendField('');
        }
      }
    }
    // Remove deleted inputs.
    while (this.getInput('ADD' + i)) {
      this.removeInput('ADD' + i);
      i++;
    }
  },
  onchange: function() {
    
  }
}



Blockly.Blocks['set_context_container'] = {
  /**
   * Mutator block for list container.
   * @this {Blockly.Block}
   */
  init: function() {
    this.appendDummyInput()
        .appendField('context');
    this.appendStatementInput('STACK');
    this.setColour(450);
    this.setTooltip('here');
    this.contextMenu = false;
  }
};

Blockly.Blocks['set_context_declaration'] = {
  /**
   * Mutator block for adding items.
   * @this {Blockly.Block}
   */
  init: function() {
    this.appendDummyInput()
        .appendField('declaration');
    this.setPreviousStatement(true);
    this.setNextStatement(true);
    this.setColour(450);
    this.setTooltip('add a declaration to the context');
    this.contextMenu = false;
  }
};
